/-
# Market maker (`lem:fpl`, `def:markemaker`, `lem:mm`)

The finite-dimensional fixed-point argument behind the paper's market maker, and the
computable rational prices it produces.  The analytic layer below deliberately works with
the actual `Strategy` representation, including repeated occurrences of one sentence:
`shares` aggregates all positions in a sentence before the price-adjustment map is formed.
-/
import LogicalInduction.Construction.Brouwer
import LogicalInduction.Framework.Affine

namespace LogicalInduction

open Classical Set Function

/-- All Boolean lists of exactly the requested length, in a fixed executable order. -/
def allBoolLists : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
      (allBoolLists n).map (false :: ·) ++ (allBoolLists n).map (true :: ·)

lemma mem_allBoolLists_iff : ∀ {n : ℕ} {xs : List Bool},
    xs ∈ allBoolLists n ↔ xs.length = n := by
  intro n
  induction n with
  | zero => intro xs; simp [allBoolLists]
  | succ n ih =>
      intro xs
      cases xs with
      | nil => simp [allBoolLists]
      | cons b xs => cases b <;> simp [allBoolLists, ih]

namespace Strategy

private lemma sum_map_eq_fin {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      simp [Fin.sum_univ_succ]

/-- The finite set of sentences on which a strategy takes a position. -/
def support {n : ℕ} (T : Strategy n) : Finset Sentence :=
  T.trades.toFinset.image Prod.snd

lemma snd_mem_support {n : ℕ} (T : Strategy n) {p : EF × Sentence}
    (hp : p ∈ T.trades) : p.2 ∈ T.support := by
  simp only [support, Finset.mem_image]
  exact ⟨p, by simpa using hp, rfl⟩

/-- The sentence represented by coordinate `i` in the finite-dimensional price cube. -/
noncomputable def coordinateSentence {n : ℕ} (T : Strategy n)
    (i : Fin (Fintype.card ↥T.support)) : Sentence :=
  ((Fintype.equivFin (↥T.support)).symm i : ↥T.support)

/-- The aggregate number of shares of `φ` bought by a strategy at history `V`.

Aggregation is load-bearing: the syntax permits the same sentence to occur more than once,
whereas a valuation assigns it only one price. -/
noncomputable def shares {n : ℕ} (T : Strategy n) (V : History) (φ : Sentence) : ℝ :=
  ∑ i : Fin T.trades.length with (T.trades.get i).2 = φ, (T.trades.get i).1.denote V

/-- Regroup the occurrence-list semantics of a strategy by its finite sentence support. -/
lemma value_eq_sum_support {n : ℕ} (T : Strategy n) (V : History)
    (w : Sentence → ℝ) :
    T.value V w = ∑ φ ∈ T.support, T.shares V φ * (w φ - V n φ) := by
  let term : Fin T.trades.length → ℝ := fun i =>
    (T.trades.get i).1.denote V * (w (T.trades.get i).2 - V n (T.trades.get i).2)
  have hvalue : T.value V w = ∑ i, term i := by
    rw [Strategy.value]
    exact sum_map_eq_fin T.trades _
  rw [hvalue]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ)
    (t := T.support)
    (g := fun i : Fin T.trades.length => (T.trades.get i).2)
    (fun i _ => T.snd_mem_support (List.get_mem T.trades i)) term]
  apply Finset.sum_congr rfl
  intro φ hφ
  rw [shares, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hsentence : (T.trades.get i).2 = φ := (Finset.mem_filter.mp hi).2
  simp only [term]
  rw [hsentence]

end Strategy

/-! Raw trade-list counterparts used at the compiler boundary.  A `Strategy n` carries
only one computational field, its list of trades; the rank proof is erased by evaluation.
These definitions make that erasure explicit and avoid a value-dependent `Strategy n`
type in the primitive-recursive compiler. -/

def tradeListSupport (trades : List (EF × Sentence)) : Finset Sentence :=
  trades.toFinset.image Prod.snd

def tradeListMarketValueRat (trades : List (EF × Sentence)) (n : ℕ)
    (Q : ℕ → Sentence → ℚ) (w : Sentence → ℚ) : ℚ :=
  (trades.map fun p => p.1.denoteRat Q * (w p.2 - Q n p.2)).sum

@[simp] theorem tradeListSupport_strategy {n : ℕ} (T : Strategy n) :
    tradeListSupport T.trades = T.support := by
  rfl

/-! ## The finite-dimensional current-price cube -/

/-- Interpret a cube point as a valuation, setting sentences outside the strategy support
to zero.  The use of `Fintype.equivFin` is only a finite-coordinate enumeration. -/
noncomputable def strategyValuation {n : ℕ} (T : Strategy n)
    (x : EuclideanSpace ℝ (Fin (Fintype.card ↥T.support))) : Valuation := fun φ =>
  if h : φ ∈ T.support then x (Fintype.equivFin (↥T.support) ⟨φ, h⟩) else 0

lemma strategyValuation_of_mem {n : ℕ} (T : Strategy n)
    (x : EuclideanSpace ℝ (Fin (Fintype.card ↥T.support)))
    {φ : Sentence} (hφ : φ ∈ T.support) :
    strategyValuation T x φ = x (Fintype.equivFin (↥T.support) ⟨φ, hφ⟩) := by
  simp [strategyValuation, hφ]

lemma strategyValuation_not_mem {n : ℕ} (T : Strategy n)
    (x : EuclideanSpace ℝ (Fin (Fintype.card ↥T.support)))
    {φ : Sentence} (hφ : φ ∉ T.support) :
    strategyValuation T x φ = 0 := by
  simp [strategyValuation, hφ]

@[simp] theorem strategyValuation_coordinateSentence {n : ℕ} (T : Strategy n)
    (x : EuclideanSpace ℝ (Fin (Fintype.card ↥T.support)))
    (i : Fin (Fintype.card ↥T.support)) :
    strategyValuation T x (T.coordinateSentence i) = x i := by
  let a : ↥T.support := (Fintype.equivFin (↥T.support)).symm i
  have ha : (a : Sentence) ∈ T.support := a.property
  change strategyValuation T x (a : Sentence) = x i
  rw [strategyValuation_of_mem T x ha]
  change x (Fintype.equivFin (↥T.support) a) = x i
  rw [Equiv.apply_symm_apply]

/-- Replace only the current day of a history by the cube valuation. -/
noncomputable def strategyHistory {n : ℕ} (T : Strategy n) (prior : History)
    (x : EuclideanSpace ℝ (Fin (Fintype.card ↥T.support))) : History :=
  Function.update prior n (strategyValuation T x)

lemma strategyHistory_current {n : ℕ} (T : Strategy n) (prior : History)
    (x : EuclideanSpace ℝ (Fin (Fintype.card ↥T.support))) :
    strategyHistory T prior x n = strategyValuation T x := by
  simp [strategyHistory]

lemma continuous_strategyValuation {n : ℕ} (T : Strategy n) :
    Continuous (strategyValuation T) := by
  apply continuous_pi
  intro φ
  by_cases hφ : φ ∈ T.support
  · simpa [strategyValuation, hφ] using
      ((EuclideanSpace.proj (𝕜 := ℝ)
        (Fintype.equivFin (↥T.support) ⟨φ, hφ⟩)).continuous :
        Continuous (fun x : EuclideanSpace ℝ (Fin (Fintype.card ↥T.support)) =>
          x (Fintype.equivFin (↥T.support) ⟨φ, hφ⟩)))
  · simpa [strategyValuation, hφ] using
      (continuous_const : Continuous
        (fun _ : EuclideanSpace ℝ (Fin (Fintype.card ↥T.support)) => (0 : ℝ)))

lemma continuous_strategyHistory {n : ℕ} (T : Strategy n) (prior : History) :
    Continuous (strategyHistory T prior) := by
  apply continuous_pi
  intro day
  apply continuous_pi
  intro φ
  by_cases hday : day = n
  · subst day
    simpa [strategyHistory] using
      ((continuous_apply φ).comp (continuous_strategyValuation T))
  · simpa [strategyHistory, Function.update, hday] using
      (continuous_const : Continuous
        (fun _ : EuclideanSpace ℝ (Fin (Fintype.card ↥T.support)) => prior day φ))

lemma continuous_strategyShares {n : ℕ} (T : Strategy n) (prior : History)
    (φ : Sentence) :
    Continuous (fun x : EuclideanSpace ℝ (Fin (Fintype.card ↥T.support)) =>
      T.shares (strategyHistory T prior x) φ) := by
  unfold Strategy.shares
  apply continuous_finset_sum
  intro i hi
  exact (EF.continuous_denote (T.trades.get i).1).comp
    (continuous_strategyHistory T prior)

/-- Value of the strategy at a variable current-price vector and a fixed payout table. -/
noncomputable def strategyWorldValue {n : ℕ} (T : Strategy n) (prior : History)
    (w : Sentence → ℝ) (x : EuclideanSpace ℝ (Fin (Fintype.card ↥T.support))) : ℝ :=
  T.value (strategyHistory T prior x) w

lemma continuous_strategyWorldValue {n : ℕ} (T : Strategy n) (prior : History)
    (w : Sentence → ℝ) : Continuous (strategyWorldValue T prior w) := by
  unfold strategyWorldValue
  simp_rw [Strategy.value_eq_sum_support]
  apply continuous_finset_sum
  intro φ hφ
  have hprice : Continuous (fun x : EuclideanSpace ℝ (Fin (Fintype.card ↥T.support)) =>
      strategyHistory T prior x n φ) := by
    simpa [strategyHistory] using
      ((continuous_apply φ).comp (continuous_strategyValuation T))
  exact (continuous_strategyShares T prior φ).mul
    (continuous_const.sub hprice)

/-- A finite Boolean payout table on the strategy support, extended by zero outside it. -/
def supportBitWorld {n : ℕ} (T : Strategy n) (b : ↥T.support → Bool) :
    Sentence → ℝ := fun φ =>
  if hφ : φ ∈ T.support then if b ⟨φ, hφ⟩ then 1 else 0 else 0

lemma supportBitWorld_mem_Icc {n : ℕ} (T : Strategy n)
    (b : ↥T.support → Bool) (φ : Sentence) :
    0 ≤ supportBitWorld T b φ ∧ supportBitWorld T b φ ≤ 1 := by
  by_cases hφ : φ ∈ T.support
  · cases hb : b ⟨φ, hφ⟩ <;> simp [supportBitWorld, hφ, hb]
  · simp [supportBitWorld, hφ]

/-- The compact convex price cube used by the fixed-point argument. -/
def strategyCube {n : ℕ} (T : Strategy n) :
    Set (EuclideanSpace ℝ (Fin (Fintype.card ↥T.support))) :=
  (EuclideanSpace.equiv (Fin (Fintype.card ↥T.support)) ℝ).symm ''
    Set.Icc (0 : Fin (Fintype.card ↥T.support) → ℝ) 1

/-- The paper's price-adjustment map `adj`, with all positions in one sentence aggregated. -/
noncomputable def priceAdjustment {n : ℕ} (T : Strategy n) (prior : History)
    (x : EuclideanSpace ℝ (Fin (Fintype.card ↥T.support))) :
    EuclideanSpace ℝ (Fin (Fintype.card ↥T.support)) :=
  (EuclideanSpace.equiv (Fin (Fintype.card ↥T.support)) ℝ).symm (fun i =>
    max 0 (min 1 (x i + T.shares (strategyHistory T prior x) (T.coordinateSentence i))))

lemma continuous_priceAdjustment {n : ℕ} (T : Strategy n) (prior : History) :
    Continuous (priceAdjustment T prior) := by
  apply (EuclideanSpace.equiv (Fin (Fintype.card ↥T.support)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  exact continuous_const.max (continuous_const.min
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.add
      (continuous_strategyShares T prior (T.coordinateSentence i))))

lemma priceAdjustment_mapsTo {n : ℕ} (T : Strategy n) (prior : History) :
    MapsTo (priceAdjustment T prior) (strategyCube T) (strategyCube T) := by
  intro x hx
  refine ⟨fun i => max 0 (min 1
      (x i + T.shares (strategyHistory T prior x) (T.coordinateSentence i))), ?_, rfl⟩
  constructor <;> intro i
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma mem_strategyCube_iff {n : ℕ} (T : Strategy n)
    (x : EuclideanSpace ℝ (Fin (Fintype.card ↥T.support))) :
    x ∈ strategyCube T ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  let E := EuclideanSpace.equiv (Fin (Fintype.card ↥T.support)) ℝ
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    exact ⟨hy.1 i, hy.2 i⟩
  · intro hx
    refine ⟨E x, ?_, E.symm_apply_apply x⟩
    exact ⟨fun i => (hx i).1, fun i => (hx i).2⟩

lemma isCompact_strategyCube {n : ℕ} (T : Strategy n) :
    IsCompact (strategyCube T) := by
  exact isCompact_Icc.image
    (EuclideanSpace.equiv (Fin (Fintype.card ↥T.support)) ℝ).symm.continuous

lemma convex_strategyCube {n : ℕ} (T : Strategy n) :
    Convex ℝ (strategyCube T) := by
  exact (convex_Icc (0 : Fin (Fintype.card ↥T.support) → ℝ) 1).linear_image
    (EuclideanSpace.equiv (Fin (Fintype.card ↥T.support)) ℝ).symm.toLinearMap

lemma strategyCube_nonempty {n : ℕ} (T : Strategy n) :
    (strategyCube T).Nonempty := by
  let E := EuclideanSpace.equiv (Fin (Fintype.card ↥T.support)) ℝ
  refine ⟨E.symm 0, 0, ?_, rfl⟩
  constructor <;> intro i <;> norm_num

/-! ### Rational points in the price cube -/

/-- Coordinatewise clipping to `[0,1]`. -/
noncomputable def clipPriceVector {n : ℕ} (T : Strategy n)
    (x : EuclideanSpace ℝ (Fin (Fintype.card ↥T.support))) :
    EuclideanSpace ℝ (Fin (Fintype.card ↥T.support)) :=
  (EuclideanSpace.equiv (Fin (Fintype.card ↥T.support)) ℝ).symm
    (fun i => max 0 (min 1 (x i)))

lemma continuous_clipPriceVector {n : ℕ} (T : Strategy n) :
    Continuous (clipPriceVector T) := by
  apply (EuclideanSpace.equiv (Fin (Fintype.card ↥T.support)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  exact continuous_const.max (continuous_const.min
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous)

lemma clipPriceVector_eq_self {n : ℕ} (T : Strategy n)
    {x : EuclideanSpace ℝ (Fin (Fintype.card ↥T.support))}
    (hx : x ∈ strategyCube T) : clipPriceVector T x = x := by
  apply PiLp.ext
  intro i
  have hi := (mem_strategyCube_iff T x).mp hx i
  simp [clipPriceVector, max_eq_right hi.1, min_eq_right hi.2]

/-- Embed an arbitrary rational coordinate table in Euclidean space. -/
noncomputable def rawRationalPriceVector {n : ℕ} (T : Strategy n)
    (q : Fin (Fintype.card ↥T.support) → ℚ) :
    EuclideanSpace ℝ (Fin (Fintype.card ↥T.support)) :=
  (EuclideanSpace.equiv (Fin (Fintype.card ↥T.support)) ℝ).symm
    (fun i => (q i : ℝ))

/-- The canonical bounded rational vector used by the search: clip in `ℚ`, then cast. -/
noncomputable def rationalPriceVector {n : ℕ} (T : Strategy n)
    (q : Fin (Fintype.card ↥T.support) → ℚ) :
    EuclideanSpace ℝ (Fin (Fintype.card ↥T.support)) :=
  (EuclideanSpace.equiv (Fin (Fintype.card ↥T.support)) ℝ).symm
    (fun i => ((max 0 (min 1 (q i)) : ℚ) : ℝ))

lemma rationalPriceVector_eq_clip {n : ℕ} (T : Strategy n)
    (q : Fin (Fintype.card ↥T.support) → ℚ) :
    rationalPriceVector T q = clipPriceVector T (rawRationalPriceVector T q) := by
  apply PiLp.ext
  intro i
  simp [rationalPriceVector, clipPriceVector, rawRationalPriceVector]

lemma rationalPriceVector_mem_cube {n : ℕ} (T : Strategy n)
    (q : Fin (Fintype.card ↥T.support) → ℚ) :
    rationalPriceVector T q ∈ strategyCube T := by
  rw [mem_strategyCube_iff]
  intro i
  change 0 ≤ (((max 0 (min 1 (q i)) : ℚ) : ℝ)) ∧
    (((max 0 (min 1 (q i)) : ℚ) : ℝ)) ≤ 1
  constructor
  · exact_mod_cast le_max_left (0 : ℚ) (min 1 (q i))
  · exact_mod_cast max_le (by norm_num : (0 : ℚ) ≤ 1) (min_le_left 1 (q i))

/-- Turn a support-contained valuation into its coordinate vector. -/
noncomputable def priceVectorOfValuation {n : ℕ} (T : Strategy n) (V : Valuation) :
    EuclideanSpace ℝ (Fin (Fintype.card ↥T.support)) :=
  (EuclideanSpace.equiv (Fin (Fintype.card ↥T.support)) ℝ).symm
    (fun i => V (T.coordinateSentence i))

lemma strategyValuation_priceVectorOfValuation {n : ℕ} (T : Strategy n)
    (V : Valuation) (hsupp : ∀ φ, φ ∉ T.support → V φ = 0) :
    strategyValuation T (priceVectorOfValuation T V) = V := by
  funext φ
  by_cases hφ : φ ∈ T.support
  · let i := Fintype.equivFin (↥T.support) ⟨φ, hφ⟩
    rw [strategyValuation_of_mem T _ hφ]
    simp only [priceVectorOfValuation]
    change V (T.coordinateSentence i) = V φ
    congr 2
    simp [Strategy.coordinateSentence, i]
  · rw [strategyValuation_not_mem T _ hφ, hsupp φ hφ]

lemma priceVectorOfValuation_mem_cube {n : ℕ} (T : Strategy n) (V : Valuation)
    (hV : ∀ φ, 0 ≤ V φ ∧ V φ ≤ 1) :
    priceVectorOfValuation T V ∈ strategyCube T := by
  rw [mem_strategyCube_iff]
  intro i
  simpa [priceVectorOfValuation] using hV (T.coordinateSentence i)

private lemma eq_one_of_clamp_add_eq {x s : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hs : 0 < s) (hfix : max 0 (min 1 (x + s)) = x) : x = 1 := by
  by_contra hne
  have hxlt : x < 1 := lt_of_le_of_ne hx1 hne
  have hsum0 : 0 < x + s := by linarith
  rw [max_eq_right (le_of_lt (lt_min (by norm_num) hsum0))] at hfix
  by_cases hsum1 : x + s ≤ 1
  · rw [min_eq_right hsum1] at hfix
    linarith
  · rw [min_eq_left (le_of_not_ge hsum1)] at hfix
    linarith

private lemma eq_zero_of_clamp_add_eq {x s : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hs : s < 0) (hfix : max 0 (min 1 (x + s)) = x) : x = 0 := by
  by_contra hne
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hne)
  have hsum1 : x + s ≤ 1 := by linarith
  rw [min_eq_right hsum1] at hfix
  by_cases hsum0 : 0 ≤ x + s
  · rw [max_eq_right hsum0] at hfix
    linarith
  · rw [max_eq_left (le_of_not_ge hsum0)] at hfix
    linarith

/-! ## `lem:fpl` — strategy-level fixed point -/

/-- Strong bounded-world form of the fixed point lemma.  The sign proof only uses that each
sentence pays in `[0,1]`, so it applies even to Boolean tables which are not restrictions of
one globally propositionally consistent world.  This stronger internal form is what makes
the MarketMaker acceptance test a finite decidable search over all support bit tables. -/
lemma fixed_point_lemma_bounded {n : ℕ} (T : Strategy n) (prior : History) :
    ∃ V : Valuation,
      (∀ φ, 0 ≤ V φ ∧ V φ ≤ 1) ∧
      (∀ φ, φ ∉ T.support → V φ = 0) ∧
      ∀ w : Sentence → ℝ, (∀ φ, 0 ≤ w φ ∧ w φ ≤ 1) →
        T.value (Function.update prior n V) w ≤ 0 := by
  obtain ⟨x, hx, hfix⟩ := brouwer_fixed_point
    (isCompact_strategyCube T) (convex_strategyCube T) (strategyCube_nonempty T)
    (priceAdjustment T prior) (continuous_priceAdjustment T prior).continuousOn
    (priceAdjustment_mapsTo T prior)
  have hxcube := (mem_strategyCube_iff T x).mp hx
  let V := strategyValuation T x
  refine ⟨V, ?_, ?_, ?_⟩
  · intro φ
    by_cases hφ : φ ∈ T.support
    · let i := Fintype.equivFin (↥T.support) ⟨φ, hφ⟩
      simpa [V, strategyValuation_of_mem T x hφ, i] using hxcube i
    · simp [V, strategyValuation_not_mem T x hφ]
  · intro φ hφ
    exact strategyValuation_not_mem T x hφ
  · intro w hw
    rw [Strategy.value_eq_sum_support]
    apply Finset.sum_nonpos
    intro φ hφ
    let i := Fintype.equivFin (↥T.support) ⟨φ, hφ⟩
    have hhist : Function.update prior n V = strategyHistory T prior x := by
      simp only [strategyHistory, V]
    have hcurrent : strategyHistory T prior x n φ = x i := by
      rw [strategyHistory_current, strategyValuation_of_mem T x hφ]
    have hfixedCoord := congrArg (fun z => z i) hfix
    have hclamp : max 0 (min 1
        (x i + T.shares (strategyHistory T prior x) φ)) = x i := by
      simpa [priceAdjustment, Strategy.coordinateSentence, i] using hfixedCoord
    by_cases hpos : 0 < T.shares (strategyHistory T prior x) φ
    · have hxi : x i = 1 := eq_one_of_clamp_add_eq
        (hxcube i).1 (hxcube i).2 hpos hclamp
      rw [hhist, hcurrent, hxi]
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpos) (by linarith [(hw φ).2])
    · by_cases hneg : T.shares (strategyHistory T prior x) φ < 0
      · have hxi : x i = 0 := eq_zero_of_clamp_add_eq
          (hxcube i).1 (hxcube i).2 hneg hclamp
        rw [hhist, hcurrent, hxi]
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hneg) (by linarith [(hw φ).1])
      · have hzero : T.shares (strategyHistory T prior x) φ = 0 := by linarith
        rw [hhist, hzero, zero_mul]

/-- Rational cube points are dense enough for all finitely many Boolean support worlds at
once.  This is the analytic termination theorem behind MarketMaker's brute-force search. -/
lemma exists_rationalPriceVector_good {n : ℕ} (T : Strategy n) (prior : History)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : Fin (Fintype.card ↥T.support) → ℚ,
      ∀ b : ↥T.support → Bool,
        strategyWorldValue T prior (supportBitWorld T b) (rationalPriceVector T q) < ε := by
  obtain ⟨V, hV, hsupp, hvalue⟩ := fixed_point_lemma_bounded T prior
  let x := priceVectorOfValuation T V
  have hxcube : x ∈ strategyCube T := priceVectorOfValuation_mem_cube T V hV
  let U : Set (EuclideanSpace ℝ (Fin (Fintype.card ↥T.support))) :=
    ⋂ b : ↥T.support → Bool,
      strategyWorldValue T prior (supportBitWorld T b) ⁻¹' Set.Iio ε
  have hUopen : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro b
    exact isOpen_Iio.preimage
      (continuous_strategyWorldValue T prior (supportBitWorld T b))
  have hxU : x ∈ U := by
    rw [Set.mem_iInter]
    intro b
    change strategyWorldValue T prior (supportBitWorld T b) x < ε
    have hhist : strategyHistory T prior x = Function.update prior n V := by
      simp only [strategyHistory, x, strategyValuation_priceVectorOfValuation T V hsupp]
    rw [strategyWorldValue, hhist]
    exact lt_of_le_of_lt (hvalue (supportBitWorld T b)
      (supportBitWorld_mem_Icc T b)) hε
  let preU := clipPriceVector T ⁻¹' U
  have hpreOpen : IsOpen preU :=
    hUopen.preimage (continuous_clipPriceVector T)
  have hxpre : x ∈ preU := by
    change clipPriceVector T x ∈ U
    rwa [clipPriceVector_eq_self T hxcube]
  have hdensePi : DenseRange (fun q : Fin (Fintype.card ↥T.support) → ℚ =>
      fun i => (q i : ℝ)) := by
    simpa only [Pi.map_apply] using
      (DenseRange.piMap (fun _ : Fin (Fintype.card ↥T.support) =>
        (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ))))
  have hdenseRaw : DenseRange (rawRationalPriceVector T) := by
    simpa [rawRationalPriceVector, Function.comp_def] using
      ((EuclideanSpace.equiv (Fin (Fintype.card ↥T.support)) ℝ).symm.surjective.denseRange.comp
        hdensePi
        (EuclideanSpace.equiv (Fin (Fintype.card ↥T.support)) ℝ).symm.continuous)
  obtain ⟨y, hyrange, hy⟩ := Dense.exists_mem_open
    (s := Set.range (rawRationalPriceVector T)) (U := preU)
    hdenseRaw hpreOpen ⟨x, hxpre⟩
  obtain ⟨q, hq⟩ := hyrange
  subst y
  refine ⟨q, ?_⟩
  intro b
  have hclip : clipPriceVector T (rawRationalPriceVector T q) ∈ U := hy
  rw [Set.mem_iInter] at hclip
  simpa [rationalPriceVector_eq_clip] using hclip b

/-! ## Finite rational belief states and the decidable MarketMaker test -/

/-- Lookup in a finite association list, with the first matching key winning and zero as
the finite-support default. -/
def quoteFromEntries : List (Sentence × ℚ) → Sentence → ℚ
  | [], _ => 0
  | (ψ, q) :: rest, φ => if φ = ψ then q else quoteFromEntries rest φ

@[simp] theorem quoteFromEntries_nil (φ : Sentence) : quoteFromEntries [] φ = 0 := rfl

@[simp] theorem quoteFromEntries_cons (ψ : Sentence) (q : ℚ)
    (rest : List (Sentence × ℚ)) (φ : Sentence) :
    quoteFromEntries ((ψ, q) :: rest) φ =
      if φ = ψ then q else quoteFromEntries rest φ := rfl

private lemma quoteFromEntries_map_eq {l : List Sentence} (hl : l.Nodup)
    (f : Sentence → ℚ) {φ : Sentence} (hφ : φ ∈ l) :
    quoteFromEntries (l.map fun ψ => (ψ, f ψ)) φ = f φ := by
  induction l with
  | nil => simp at hφ
  | cons ψ rest ih =>
      simp only [List.nodup_cons] at hl
      simp only [List.mem_cons] at hφ
      rcases hφ with rfl | hφ
      · simp
      · have hne : φ ≠ ψ := fun h => hl.1 (h ▸ hφ)
        simp [hne, ih hl.2 hφ]

private lemma quoteFromEntries_map_eq_zero {l : List Sentence} (f : Sentence → ℚ)
    {φ : Sentence} (hφ : φ ∉ l) :
    quoteFromEntries (l.map fun ψ => (ψ, f ψ)) φ = 0 := by
  induction l with
  | nil => rfl
  | cons ψ rest ih =>
      simp only [List.mem_cons, not_or] at hφ
      simp [hφ.1, ih hφ.2]

private lemma quoteFromEntries_eq_zero {entries : List (Sentence × ℚ)} {φ : Sentence}
    (hφ : φ ∉ entries.map Prod.fst) : quoteFromEntries entries φ = 0 := by
  induction entries with
  | nil => rfl
  | cons p rest ih =>
      have hne : φ ≠ p.1 := by
        intro heq
        apply hφ
        simp [heq]
      have hrest : φ ∉ rest.map Prod.fst := by
        intro hmem
        exact hφ (by simp [hmem])
      simp [quoteFromEntries, hne, ih hrest]

/-- A paper belief state: a rational-valued, finite-support `[0,1]` valuation represented
by a duplicate-free finite association list.  This is data, not a semantic certificate. -/
structure RationalBeliefState where
  entries : List (Sentence × ℚ)
  keys_nodup : (entries.map Prod.fst).Nodup
  bounded : ∀ p ∈ entries, 0 ≤ p.2 ∧ p.2 ≤ 1

namespace RationalBeliefState

/-- Exact rational quote, zero outside the finite entry list. -/
def quote (B : RationalBeliefState) : Sentence → ℚ := quoteFromEntries B.entries

/-- Real valuation denoted by a rational belief state. -/
def toValuation (B : RationalBeliefState) : Valuation := fun φ => (B.quote φ : ℝ)

/-- Syntactic finite support (zero-valued listed entries are harmless). -/
def support (B : RationalBeliefState) : Finset Sentence :=
  (B.entries.map Prod.fst).toFinset

lemma quote_eq_zero_of_not_mem (B : RationalBeliefState) {φ : Sentence}
    (hφ : φ ∉ B.support) : B.quote φ = 0 := by
  unfold quote
  unfold support at hφ
  have hlist : φ ∉ B.entries.map Prod.fst := by simpa using hφ
  exact quoteFromEntries_eq_zero hlist

lemma quote_mem_Icc (B : RationalBeliefState) (φ : Sentence) :
    0 ≤ B.quote φ ∧ B.quote φ ≤ 1 := by
  unfold quote
  have hb : ∀ p ∈ B.entries, 0 ≤ p.2 ∧ p.2 ≤ 1 := B.bounded
  generalize B.entries = entries at hb ⊢
  induction entries with
  | nil => norm_num [quoteFromEntries]
  | cons p rest ih =>
      simp only [quoteFromEntries]
      split
      · exact hb p (by simp)
      · exact ih (fun p hp => hb p (by simp [hp]))

lemma toValuation_mem_Icc (B : RationalBeliefState) (φ : Sentence) :
    0 ≤ B.toValuation φ ∧ B.toValuation φ ≤ 1 := by
  unfold toValuation
  constructor
  · exact_mod_cast (B.quote_mem_Icc φ).1
  · exact_mod_cast (B.quote_mem_Icc φ).2

/-- Rational quote attached to a sentence coordinate, with zero outside the support. -/
noncomputable def clippedCoordinateQuote {n : ℕ} (T : Strategy n)
    (q : Fin (Fintype.card ↥T.support) → ℚ) (φ : Sentence) : ℚ :=
  if hφ : φ ∈ T.support then
    max 0 (min 1 (q (Fintype.equivFin (↥T.support) ⟨φ, hφ⟩))) else 0

/-- Canonical belief state on a strategy's support, obtained by clipping a rational vector. -/
noncomputable def ofStrategyVector {n : ℕ} (T : Strategy n)
    (q : Fin (Fintype.card ↥T.support) → ℚ) : RationalBeliefState where
  entries := T.support.toList.map fun φ =>
    (φ, clippedCoordinateQuote T q φ)
  keys_nodup := by
    have heq : (T.support.toList.map fun φ =>
        (φ, clippedCoordinateQuote T q φ)).map Prod.fst = T.support.toList := by
      rw [List.map_map]
      change T.support.toList.map id = T.support.toList
      generalize T.support.toList = l
      induction l with
      | nil => rfl
      | cons a l ih => simp [ih]
    rw [heq]
    exact T.support.nodup_toList
  bounded := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨φ, hφ, rfl⟩ := hp
    rw [clippedCoordinateQuote, dif_pos (Finset.mem_toList.mp hφ)]
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)

lemma ofStrategyVector_support {n : ℕ} (T : Strategy n)
    (q : Fin (Fintype.card ↥T.support) → ℚ) :
    (ofStrategyVector T q).support = T.support := by
  ext φ
  simp [ofStrategyVector, support]

lemma ofStrategyVector_quote {n : ℕ} (T : Strategy n)
    (q : Fin (Fintype.card ↥T.support) → ℚ) {φ : Sentence} (hφ : φ ∈ T.support) :
    (ofStrategyVector T q).quote φ =
      max 0 (min 1 (q (Fintype.equivFin (↥T.support) ⟨φ, hφ⟩))) := by
  rw [quote, show (ofStrategyVector T q).entries =
      T.support.toList.map fun ψ => (ψ, clippedCoordinateQuote T q ψ) from rfl,
    quoteFromEntries_map_eq T.support.nodup_toList (clippedCoordinateQuote T q)
    (Finset.mem_toList.mpr hφ)]
  simp [clippedCoordinateQuote, hφ]

lemma ofStrategyVector_toValuation {n : ℕ} (T : Strategy n)
    (q : Fin (Fintype.card ↥T.support) → ℚ) :
    (ofStrategyVector T q).toValuation = strategyValuation T (rationalPriceVector T q) := by
  funext φ
  by_cases hφ : φ ∈ T.support
  · rw [toValuation, ofStrategyVector_quote T q hφ,
      strategyValuation_of_mem T _ hφ]
    rfl
  · rw [toValuation, quote_eq_zero_of_not_mem]
    · simp [strategyValuation_not_mem T _ hφ]
    · simpa [ofStrategyVector_support T q] using hφ

end RationalBeliefState

/-- Exact rational table denoted by a finite chronological list of belief states. -/
def rationalHistory (past : List RationalBeliefState) : ℕ → Sentence → ℚ :=
  fun day φ => match past[day]? with
    | some B => B.quote φ
    | none => 0

/-- Real history obtained by casting the exact finite rational table. -/
def beliefHistory (past : List RationalBeliefState) : History :=
  fun day φ => (rationalHistory past day φ : ℝ)

lemma beliefHistory_eq_ratCast (past : List RationalBeliefState) (day : ℕ)
    (φ : Sentence) : beliefHistory past day φ = (rationalHistory past day φ : ℝ) := rfl

/-- Replace day `n` of a rational history by a candidate belief state. -/
def candidateRationalHistory (past : List RationalBeliefState) (n : ℕ)
    (B : RationalBeliefState) : ℕ → Sentence → ℚ :=
  Function.update (rationalHistory past) n B.quote

lemma candidateHistory_cast (past : List RationalBeliefState) (n : ℕ)
    (B : RationalBeliefState) :
    (fun day φ => (candidateRationalHistory past n B day φ : ℝ)) =
      Function.update (beliefHistory past) n B.toValuation := by
  funext day φ
  by_cases hday : day = n <;> simp [candidateRationalHistory, beliefHistory,
    RationalBeliefState.toValuation, Function.update, hday]

namespace Strategy

/-- Exact rational evaluation of a strategy. -/
def marketValueRat {n : ℕ} (T : Strategy n) (Q : ℕ → Sentence → ℚ)
    (w : Sentence → ℚ) : ℚ :=
  (T.trades.map fun p => p.1.denoteRat Q * (w p.2 - Q n p.2)).sum

lemma value_eq_marketRatCast {n : ℕ} (T : Strategy n) (P : History)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, P day φ = (Q day φ : ℝ))
    (wR : Sentence → ℝ) (wQ : Sentence → ℚ)
    (hw : ∀ φ, wR φ = (wQ φ : ℝ)) :
    T.value P wR = (T.marketValueRat Q wQ : ℝ) := by
  unfold Strategy.value marketValueRat
  induction T.trades with
  | nil => simp
  | cons p rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [EF.denote_eq_ratCast p.1 P Q hQ, hw p.2, hQ n p.2, ih]
      norm_cast

end Strategy

@[simp] theorem tradeListMarketValueRat_strategy {n : ℕ} (T : Strategy n)
    (Q : ℕ → Sentence → ℚ) (w : Sentence → ℚ) :
    tradeListMarketValueRat T.trades n Q w = T.marketValueRat Q w := by
  rfl

/-- Rational version of a support bit table. -/
def supportBitWorldRat {n : ℕ} (T : Strategy n) (b : ↥T.support → Bool) :
    Sentence → ℚ := fun φ =>
  if hφ : φ ∈ T.support then if b ⟨φ, hφ⟩ then 1 else 0 else 0

/-! First-order bit-list presentation of the finite support worlds. -/

def supportSentenceList (S : Finset Sentence) : List Sentence :=
  let r : Sentence → Sentence → Prop := fun φ ψ =>
    Encodable.encode φ ≤ Encodable.encode ψ
  letI : IsTrans Sentence r :=
    ⟨fun _ _ _ hab hbc => hab.trans hbc⟩
  letI : Std.Antisymm r :=
    ⟨fun _ _ hab hba => Encodable.encode_injective (le_antisymm hab hba)⟩
  letI : Std.Total r :=
    ⟨fun φ ψ => le_total (Encodable.encode φ) (Encodable.encode ψ)⟩
  S.sort r

def supportAssignmentOfList (S : Finset Sentence) (xs : List Bool) : S → Bool := fun φ =>
  xs.getD ((supportSentenceList S).idxOf φ.1) false

def supportBitWorldRatFromList {n : ℕ} (T : Strategy n) (xs : List Bool) :
    Sentence → ℚ := fun φ =>
  if _hφ : φ ∈ T.support then
    if xs.getD ((supportSentenceList T.support).idxOf φ) false then 1 else 0
  else 0

def tradeListSupportBitWorldRatFromList (trades : List (EF × Sentence))
    (xs : List Bool) : Sentence → ℚ := fun φ =>
  if _hφ : φ ∈ tradeListSupport trades then
    if xs.getD ((supportSentenceList (tradeListSupport trades)).idxOf φ) false then 1 else 0
  else 0

@[simp] theorem tradeListSupportBitWorldRatFromList_strategy {n : ℕ}
    (T : Strategy n) (xs : List Bool) :
    tradeListSupportBitWorldRatFromList T.trades xs =
      supportBitWorldRatFromList T xs := by
  rfl

lemma supportBitWorldRatFromList_eq {n : ℕ} (T : Strategy n) (xs : List Bool) :
    supportBitWorldRatFromList T xs =
      supportBitWorldRat T (supportAssignmentOfList T.support xs) := by
  funext φ
  by_cases hφ : φ ∈ T.support
  · simp [supportBitWorldRatFromList, supportBitWorldRat,
      supportAssignmentOfList, hφ]
  · simp [supportBitWorldRatFromList, supportBitWorldRat, hφ]

def supportAssignmentList (S : Finset Sentence) (b : S → Bool) : List Bool :=
  (supportSentenceList S).map fun φ => if hφ : φ ∈ S then b ⟨φ, hφ⟩ else false

@[simp] theorem supportAssignmentList_length (S : Finset Sentence) (b : S → Bool) :
    (supportAssignmentList S b).length = S.card := by
  simp [supportAssignmentList, supportSentenceList]

lemma supportAssignmentOfList_supportAssignmentList (S : Finset Sentence)
    (b : S → Bool) :
    supportAssignmentOfList S (supportAssignmentList S b) = b := by
  funext φ
  unfold supportAssignmentOfList supportAssignmentList
  have hmem : φ.1 ∈ supportSentenceList S := by
    simp [supportSentenceList, φ.2]
  have hidx : (supportSentenceList S).idxOf φ.1 < (supportSentenceList S).length :=
    List.idxOf_lt_length_of_mem hmem
  rw [List.getD_eq_getElem _ _ (by simpa using hidx), List.getElem_map,
    List.getElem_idxOf hidx]
  simp [φ.2]

lemma supportBitWorld_eq_ratCast {n : ℕ} (T : Strategy n)
    (b : ↥T.support → Bool) (φ : Sentence) :
    supportBitWorld T b φ = (supportBitWorldRat T b φ : ℝ) := by
  by_cases hφ : φ ∈ T.support
  · cases hb : b ⟨φ, hφ⟩ <;> simp [supportBitWorld, supportBitWorldRat, hφ, hb]
  · simp [supportBitWorld, supportBitWorldRat, hφ]

/-- The exact decidable predicate tested by MarketMaker's enumeration.  It contains only
finite syntax/rational arithmetic and quantification over a finite Boolean table. -/
def MarketMakerAccepts {n : ℕ} (T : Strategy n) (past : List RationalBeliefState)
    (ε : ℚ) (B : RationalBeliefState) : Prop :=
  B.support ⊆ T.support ∧
    ∀ b : ↥T.support → Bool,
      T.marketValueRat (candidateRationalHistory past n B) (supportBitWorldRat T b) ≤ ε

instance MarketMakerAccepts.instDecidable {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (B : RationalBeliefState) :
    Decidable (MarketMakerAccepts T past ε B) := by
  unfold MarketMakerAccepts
  infer_instance

/-- First-order finite-list presentation of the same MarketMaker acceptance test. -/
def MarketMakerAcceptsFromLists {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (B : RationalBeliefState) : Prop :=
  B.support ⊆ T.support ∧
    ∀ xs ∈ allBoolLists T.support.card,
      T.marketValueRat (candidateRationalHistory past n B)
        (supportBitWorldRatFromList T xs) ≤ ε

/-- Completely first-order MarketMaker acceptance: the day and raw trade list are data. -/
def MarketMakerAcceptsTradeList (trades : List (EF × Sentence)) (n : ℕ)
    (past : List RationalBeliefState) (ε : ℚ) (B : RationalBeliefState) : Prop :=
  B.support ⊆ tradeListSupport trades ∧
    ∀ xs ∈ allBoolLists (tradeListSupport trades).card,
      tradeListMarketValueRat trades n (candidateRationalHistory past n B)
        (tradeListSupportBitWorldRatFromList trades xs) ≤ ε

instance MarketMakerAcceptsTradeList.instDecidable (trades : List (EF × Sentence))
    (n : ℕ) (past : List RationalBeliefState) (ε : ℚ) (B : RationalBeliefState) :
    Decidable (MarketMakerAcceptsTradeList trades n past ε B) := by
  unfold MarketMakerAcceptsTradeList
  infer_instance

lemma marketMakerAcceptsTradeList_iff {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (B : RationalBeliefState) :
    MarketMakerAcceptsTradeList T.trades n past ε B ↔
      MarketMakerAcceptsFromLists T past ε B := by
  rfl

instance MarketMakerAcceptsFromLists.instDecidable {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (B : RationalBeliefState) :
    Decidable (MarketMakerAcceptsFromLists T past ε B) := by
  unfold MarketMakerAcceptsFromLists
  infer_instance

lemma marketMakerAcceptsFromLists_iff {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (B : RationalBeliefState) :
    MarketMakerAcceptsFromLists T past ε B ↔ MarketMakerAccepts T past ε B := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro b
    let xs := supportAssignmentList T.support b
    have hxs : xs ∈ allBoolLists T.support.card :=
      mem_allBoolLists_iff.mpr (supportAssignmentList_length T.support b)
    have hv := h.2 xs hxs
    rw [supportBitWorldRatFromList_eq,
      supportAssignmentOfList_supportAssignmentList] at hv
    exact hv
  · intro h
    refine ⟨h.1, ?_⟩
    intro xs hxs
    rw [supportBitWorldRatFromList_eq]
    exact h.2 (supportAssignmentOfList T.support xs)

/-- The acceptance predicate is semantically sound for all Boolean support tables. -/
lemma MarketMakerAccepts.worldValue_le {n : ℕ} {T : Strategy n}
    {past : List RationalBeliefState} {ε : ℚ} {B : RationalBeliefState}
    (h : MarketMakerAccepts T past ε B) (b : ↥T.support → Bool) :
    T.value (Function.update (beliefHistory past) n B.toValuation)
      (supportBitWorld T b) ≤ (ε : ℝ) := by
  have hcast := T.value_eq_marketRatCast
    (Function.update (beliefHistory past) n B.toValuation)
    (candidateRationalHistory past n B)
    (fun day φ => by
      have hc := congrFun (congrFun (candidateHistory_cast past n B) day) φ
      exact hc.symm)
    (supportBitWorld T b) (supportBitWorldRat T b)
    (supportBitWorld_eq_ratCast T b)
  rw [hcast]
  exact_mod_cast h.2 b

/-- Every MarketMaker search instance has an accepted finite rational candidate. -/
lemma exists_marketMakerAccepts {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) {ε : ℚ} (hε : 0 < ε) :
    ∃ B : RationalBeliefState, MarketMakerAccepts T past ε B := by
  obtain ⟨q, hq⟩ := exists_rationalPriceVector_good T (beliefHistory past)
    (ε := (ε : ℝ)) (by exact_mod_cast hε)
  let B := RationalBeliefState.ofStrategyVector T q
  refine ⟨B, ?_, ?_⟩
  · intro φ hφ
    simpa [B, RationalBeliefState.ofStrategyVector_support T q] using hφ
  · intro b
    have hreal := hq b
    have hB : B.toValuation = strategyValuation T (rationalPriceVector T q) :=
      RationalBeliefState.ofStrategyVector_toValuation T q
    have hhist : Function.update (beliefHistory past) n B.toValuation =
        strategyHistory T (beliefHistory past) (rationalPriceVector T q) := by
      simp [strategyHistory, hB]
    have hsound : T.value (Function.update (beliefHistory past) n B.toValuation)
        (supportBitWorld T b) =
        (T.marketValueRat (candidateRationalHistory past n B) (supportBitWorldRat T b) : ℝ) := by
      apply T.value_eq_marketRatCast
      · intro day φ
        have hc := congrFun (congrFun (candidateHistory_cast past n B) day) φ
        exact hc.symm
      · exact supportBitWorld_eq_ratCast T b
    rw [strategyWorldValue, ← hhist, hsound] at hreal
    have hle : (T.marketValueRat (candidateRationalHistory past n B)
        (supportBitWorldRat T b) : ℝ) ≤ (ε : ℝ) := le_of_lt hreal
    exact_mod_cast hle

/-! ### The literal first-successful-candidate search -/

namespace RationalBeliefState

/-- Validate a raw finite association list as a rational belief state. -/
def ofEntries? (entries : List (Sentence × ℚ)) : Option RationalBeliefState :=
  if hn : (entries.map Prod.fst).Nodup then
    if hb : ∀ p ∈ entries, 0 ≤ p.2 ∧ p.2 ≤ 1 then
      some ⟨entries, hn, hb⟩
    else none
  else none

lemma ofEntries?_self (B : RationalBeliefState) : ofEntries? B.entries = some B := by
  simp only [ofEntries?, dif_pos B.keys_nodup, dif_pos B.bounded]

end RationalBeliefState

/-- Decode and validate candidate number `k`.  This is the enumeration searched by
MarketMaker; every valid finite rational belief state occurs at its list encoding. -/
def marketMakerCandidate (k : ℕ) : Option RationalBeliefState :=
  (Encodable.decode (α := List (Sentence × ℚ)) k).bind
    RationalBeliefState.ofEntries?

lemma marketMakerCandidate_encode (B : RationalBeliefState) :
    marketMakerCandidate (Encodable.encode B.entries) = some B := by
  simp [marketMakerCandidate, Encodable.encodek, RationalBeliefState.ofEntries?_self]

/-- Candidate number `k` is a successful output for this MarketMaker invocation. -/
def MarketMakerCandidateAccepts {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (k : ℕ) : Prop :=
  ∃ B, marketMakerCandidate k = some B ∧ MarketMakerAccepts T past ε B

instance MarketMakerCandidateAccepts.instDecidable {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (k : ℕ) :
    Decidable (MarketMakerCandidateAccepts T past ε k) := by
  unfold MarketMakerCandidateAccepts
  cases hB : marketMakerCandidate k with
  | none =>
      exact isFalse (by rintro ⟨B, h, _⟩; simp at h)
  | some B =>
      exact decidable_of_iff (MarketMakerAccepts T past ε B) (by
        constructor
        · intro h; exact ⟨B, rfl, h⟩
        · rintro ⟨B', hB', h⟩
          cases hB'
          exact h)

def MarketMakerCandidateAcceptsFromLists {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (k : ℕ) : Prop :=
  ∃ B, marketMakerCandidate k = some B ∧ MarketMakerAcceptsFromLists T past ε B

def MarketMakerCandidateAcceptsTradeList (trades : List (EF × Sentence)) (n : ℕ)
    (past : List RationalBeliefState) (ε : ℚ) (k : ℕ) : Prop :=
  ∃ B, marketMakerCandidate k = some B ∧
    MarketMakerAcceptsTradeList trades n past ε B

instance MarketMakerCandidateAcceptsTradeList.instDecidable
    (trades : List (EF × Sentence)) (n : ℕ)
    (past : List RationalBeliefState) (ε : ℚ) (k : ℕ) :
    Decidable (MarketMakerCandidateAcceptsTradeList trades n past ε k) := by
  unfold MarketMakerCandidateAcceptsTradeList
  cases hB : marketMakerCandidate k with
  | none =>
      exact isFalse (by rintro ⟨B, h, _⟩; simp at h)
  | some B =>
      exact decidable_of_iff (MarketMakerAcceptsTradeList trades n past ε B) (by
        constructor
        · intro h; exact ⟨B, rfl, h⟩
        · rintro ⟨B', hB', h⟩
          cases hB'
          exact h)

instance MarketMakerCandidateAcceptsFromLists.instDecidable {n : ℕ}
    (T : Strategy n) (past : List RationalBeliefState) (ε : ℚ) (k : ℕ) :
    Decidable (MarketMakerCandidateAcceptsFromLists T past ε k) := by
  unfold MarketMakerCandidateAcceptsFromLists
  cases hB : marketMakerCandidate k with
  | none =>
      exact isFalse (by rintro ⟨B, h, _⟩; simp at h)
  | some B =>
      exact decidable_of_iff (MarketMakerAcceptsFromLists T past ε B) (by
        constructor
        · intro h; exact ⟨B, rfl, h⟩
        · rintro ⟨B', hB', h⟩
          cases hB'
          exact h)

lemma marketMakerCandidateAcceptsFromLists_iff {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (k : ℕ) :
    MarketMakerCandidateAcceptsFromLists T past ε k ↔
      MarketMakerCandidateAccepts T past ε k := by
  unfold MarketMakerCandidateAcceptsFromLists MarketMakerCandidateAccepts
  constructor
  · rintro ⟨B, hB, h⟩
    exact ⟨B, hB, (marketMakerAcceptsFromLists_iff T past ε B).mp h⟩
  · rintro ⟨B, hB, h⟩
    exact ⟨B, hB, (marketMakerAcceptsFromLists_iff T past ε B).mpr h⟩

lemma marketMakerCandidateAcceptsTradeList_iff {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (k : ℕ) :
    MarketMakerCandidateAcceptsTradeList T.trades n past ε k ↔
      MarketMakerCandidateAcceptsFromLists T past ε k := by
  unfold MarketMakerCandidateAcceptsTradeList MarketMakerCandidateAcceptsFromLists
  constructor
  · rintro ⟨B, hB, h⟩
    exact ⟨B, hB, (marketMakerAcceptsTradeList_iff T past ε B).mp h⟩
  · rintro ⟨B, hB, h⟩
    exact ⟨B, hB, (marketMakerAcceptsTradeList_iff T past ε B).mpr h⟩

lemma exists_marketMakerCandidateAccepts {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) {ε : ℚ} (hε : 0 < ε) :
    ∃ k, MarketMakerCandidateAccepts T past ε k := by
  obtain ⟨B, hB⟩ := exists_marketMakerAccepts T past hε
  exact ⟨Encodable.encode B.entries, B, marketMakerCandidate_encode B, hB⟩

/-- Index of the first accepted candidate in the explicit enumeration. -/
noncomputable def marketMakerIndex {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (hε : 0 < ε) : ℕ :=
  Nat.find (exists_marketMakerCandidateAccepts T past hε)

lemma marketMakerIndex_spec {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (hε : 0 < ε) :
    MarketMakerCandidateAccepts T past ε (marketMakerIndex T past ε hε) :=
  Nat.find_spec (exists_marketMakerCandidateAccepts T past hε)

/-- Executable bounded search for the first successful candidate index below `fuel`.
The recursion is a literal clock: one candidate is decoded and checked per successor step. -/
def marketMakerSearchIndexUpTo {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 =>
      match marketMakerSearchIndexUpTo T past ε fuel with
      | some k => some k
      | none =>
          if MarketMakerCandidateAccepts T past ε fuel then some fuel else none

/-- First-order Boolean-list search, extensionally identical to the semantic search. -/
def marketMakerSearchIndexUpToFromLists {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 =>
      match marketMakerSearchIndexUpToFromLists T past ε fuel with
      | some k => some k
      | none =>
          if MarketMakerCandidateAcceptsFromLists T past ε fuel then some fuel else none

def marketMakerSearchIndexUpToTradeList (trades : List (EF × Sentence)) (n : ℕ)
    (past : List RationalBeliefState) (ε : ℚ) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 =>
      match marketMakerSearchIndexUpToTradeList trades n past ε fuel with
      | some k => some k
      | none =>
          if MarketMakerCandidateAcceptsTradeList trades n past ε fuel then
            some fuel
          else none

lemma marketMakerSearchIndexUpToTradeList_eq {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (fuel : ℕ) :
    marketMakerSearchIndexUpToTradeList T.trades n past ε fuel =
      marketMakerSearchIndexUpToFromLists T past ε fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp only [marketMakerSearchIndexUpToTradeList,
        marketMakerSearchIndexUpToFromLists, ih]
      cases hsearch : marketMakerSearchIndexUpToFromLists T past ε fuel with
      | some k => rfl
      | none =>
          by_cases h : MarketMakerCandidateAcceptsTradeList T.trades n past ε fuel
          · have h' : MarketMakerCandidateAcceptsFromLists T past ε fuel :=
              (marketMakerCandidateAcceptsTradeList_iff T past ε fuel).mp h
            simp [h, h']
          · have h' : ¬MarketMakerCandidateAcceptsFromLists T past ε fuel := by
              exact fun h' => h
                ((marketMakerCandidateAcceptsTradeList_iff T past ε fuel).mpr h')
            simp [h, h']

lemma marketMakerSearchIndexUpToFromLists_eq {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (fuel : ℕ) :
    marketMakerSearchIndexUpToFromLists T past ε fuel =
      marketMakerSearchIndexUpTo T past ε fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp only [marketMakerSearchIndexUpToFromLists, marketMakerSearchIndexUpTo, ih]
      cases hsearch : marketMakerSearchIndexUpTo T past ε fuel with
      | some k => rfl
      | none =>
          by_cases h : MarketMakerCandidateAcceptsFromLists T past ε fuel
          · have h' : MarketMakerCandidateAccepts T past ε fuel :=
              (marketMakerCandidateAcceptsFromLists_iff T past ε fuel).mp h
            simp [h, h']
          · have h' : ¬MarketMakerCandidateAccepts T past ε fuel := by
              exact fun h' => h
                ((marketMakerCandidateAcceptsFromLists_iff T past ε fuel).mpr h')
            simp [h, h']

lemma marketMakerSearchIndexUpTo_eq_none_iff {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (fuel : ℕ) :
    marketMakerSearchIndexUpTo T past ε fuel = none ↔
      ∀ k, k < fuel → ¬ MarketMakerCandidateAccepts T past ε k := by
  induction fuel with
  | zero => simp [marketMakerSearchIndexUpTo]
  | succ fuel ih =>
      cases hs : marketMakerSearchIndexUpTo T past ε fuel with
      | none =>
          by_cases hacc : MarketMakerCandidateAccepts T past ε fuel
          · constructor
            · intro h
              rw [marketMakerSearchIndexUpTo, hs, if_pos hacc] at h
              exact (Option.some_ne_none fuel h).elim
            · intro hall
              exact (hall fuel (Nat.lt_succ_self fuel) hacc).elim
          · constructor
            · intro _ k hk
              have hle : k ≤ fuel := Nat.lt_succ_iff.mp hk
              rcases lt_or_eq_of_le hle with hlt | rfl
              · exact (ih.mp hs) k hlt
              · exact hacc
            · intro _hall
              simp [marketMakerSearchIndexUpTo, hs, hacc]
      | some k =>
          constructor
          · intro h
            rw [marketMakerSearchIndexUpTo, hs] at h
            exact (Option.some_ne_none k h).elim
          · intro hall
            have hnone := ih.mpr (fun j hj => hall j (by omega))
            exact (Option.some_ne_none k (hs.symm.trans hnone)).elim

/-- Decode the bounded search's result.  Unlike an opaque choice, this function reduces
for every concrete `fuel`, strategy, history, and rational tolerance. -/
def marketMakerSearchUpTo {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (fuel : ℕ) :
    Option RationalBeliefState :=
  (marketMakerSearchIndexUpTo T past ε fuel).bind marketMakerCandidate

def marketMakerSearchUpToFromLists {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (fuel : ℕ) :
    Option RationalBeliefState :=
  (marketMakerSearchIndexUpToFromLists T past ε fuel).bind marketMakerCandidate

def marketMakerSearchUpToTradeList (trades : List (EF × Sentence)) (n : ℕ)
    (past : List RationalBeliefState) (ε : ℚ) (fuel : ℕ) :
    Option RationalBeliefState :=
  (marketMakerSearchIndexUpToTradeList trades n past ε fuel).bind marketMakerCandidate

lemma marketMakerSearchUpToTradeList_eq {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (fuel : ℕ) :
    marketMakerSearchUpToTradeList T.trades n past ε fuel =
      marketMakerSearchUpToFromLists T past ε fuel := by
  unfold marketMakerSearchUpToTradeList marketMakerSearchUpToFromLists
  rw [marketMakerSearchIndexUpToTradeList_eq]

lemma marketMakerSearchUpToFromLists_eq {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (fuel : ℕ) :
    marketMakerSearchUpToFromLists T past ε fuel =
      marketMakerSearchUpTo T past ε fuel := by
  unfold marketMakerSearchUpToFromLists marketMakerSearchUpTo
  rw [marketMakerSearchIndexUpToFromLists_eq]

lemma marketMakerSearchIndexUpTo_mono_success {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) {fuel fuel' k : ℕ}
    (hff : fuel ≤ fuel')
    (h : marketMakerSearchIndexUpTo T past ε fuel = some k) :
    marketMakerSearchIndexUpTo T past ε fuel' = some k := by
  induction fuel', hff using Nat.le_induction with
  | base => exact h
  | succ fuel' _ ih =>
      simp [marketMakerSearchIndexUpTo, ih]

lemma marketMakerSearchUpTo_mono_success {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) {fuel fuel' : ℕ}
    {B : RationalBeliefState} (hff : fuel ≤ fuel')
    (h : marketMakerSearchUpTo T past ε fuel = some B) :
    marketMakerSearchUpTo T past ε fuel' = some B := by
  unfold marketMakerSearchUpTo at h ⊢
  cases hs : marketMakerSearchIndexUpTo T past ε fuel with
  | none => simp [hs] at h
  | some k =>
      rw [hs] at h
      rw [marketMakerSearchIndexUpTo_mono_success T past ε hff hs]
      exact h

private lemma marketMakerCandidate_index_isSome {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (hε : 0 < ε) :
    (marketMakerCandidate (marketMakerIndex T past ε hε)).isSome = true := by
  obtain ⟨B, hB, _⟩ := marketMakerIndex_spec T past ε hε
  rw [hB]
  rfl

/-- **`MarketMaker`** (`def:markemaker`): the decoded first rational candidate whose
finite exact-arithmetic check succeeds.  Totality comes from the analytic existence proof;
execution is the bounded clock `marketMakerSearchUpTo` at the certified stopping time. -/
noncomputable def MarketMaker {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (hε : 0 < ε) : RationalBeliefState :=
  (marketMakerCandidate (marketMakerIndex T past ε hε)).get
    (marketMakerCandidate_index_isSome T past ε hε)

lemma MarketMaker_candidate {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (hε : 0 < ε) :
    marketMakerCandidate (marketMakerIndex T past ε hε) =
      some (MarketMaker T past ε hε) :=
  (Option.some_get (marketMakerCandidate_index_isSome T past ε hε)).symm

lemma MarketMaker_accepts {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (hε : 0 < ε) :
    MarketMakerAccepts T past ε (MarketMaker T past ε hε) := by
  obtain ⟨B, hB, haccepts⟩ := marketMakerIndex_spec T past ε hε
  rw [MarketMaker_candidate T past ε hε] at hB
  cases hB
  exact haccepts

lemma MarketMaker_search_clock {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (hε : 0 < ε) :
    marketMakerSearchUpTo T past ε (marketMakerIndex T past ε hε + 1) =
      some (MarketMaker T past ε hε) := by
  have hnone : marketMakerSearchIndexUpTo T past ε
      (marketMakerIndex T past ε hε) = none :=
    (marketMakerSearchIndexUpTo_eq_none_iff T past ε _).2
      (fun k hk => Nat.find_min (exists_marketMakerCandidateAccepts T past hε) hk)
  have haccepts := marketMakerIndex_spec T past ε hε
  simp [marketMakerSearchUpTo, marketMakerSearchIndexUpTo, hnone, haccepts,
    MarketMaker_candidate T past ε hε]

lemma MarketMaker_search_of_clock_le {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (hε : 0 < ε) {fuel : ℕ}
    (hclock : marketMakerIndex T past ε hε + 1 ≤ fuel) :
    marketMakerSearchUpTo T past ε fuel = some (MarketMaker T past ε hε) :=
  marketMakerSearchUpTo_mono_success T past ε hclock
    (MarketMaker_search_clock T past ε hε)

/-- Any successful bounded search already returns the canonical first accepted candidate;
the fuel bound affects termination only, never the result. -/
lemma MarketMaker_searchUpTo_sound {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (hε : 0 < ε)
    {fuel : ℕ} {B : RationalBeliefState}
    (h : marketMakerSearchUpTo T past ε fuel = some B) :
    B = MarketMaker T past ε hε := by
  let common := max fuel (marketMakerIndex T past ε hε + 1)
  have hB : marketMakerSearchUpTo T past ε common = some B :=
    marketMakerSearchUpTo_mono_success T past ε (Nat.le_max_left _ _) h
  have hMM : marketMakerSearchUpTo T past ε common =
      some (MarketMaker T past ε hε) :=
    MarketMaker_search_of_clock_le T past ε hε (Nat.le_max_right _ _)
  exact Option.some.inj (hB.symm.trans hMM)

/-- The paper's 0-based error allowance: day `n` corresponds to paper day `n+1`. -/
def marketMakerError (n : ℕ) : ℚ := 1 / (2 : ℚ) ^ (n + 1)

lemma marketMakerError_pos (n : ℕ) : 0 < marketMakerError n := by
  unfold marketMakerError
  exact div_pos (by norm_num) (pow_pos (by norm_num) _)

lemma MarketMaker_support {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (hε : 0 < ε) :
    (MarketMaker T past ε hε).support ⊆ T.support :=
  (MarketMaker_accepts T past ε hε).1

lemma MarketMaker_range {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (hε : 0 < ε) (φ : Sentence) :
    (MarketMaker T past ε hε).toValuation φ ∈ Set.Icc (0 : ℝ) 1 :=
  (MarketMaker T past ε hε).toValuation_mem_Icc φ

lemma MarketMaker_zero_of_not_support {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (hε : 0 < ε)
    {φ : Sentence} (hφ : φ ∉ T.support) :
    (MarketMaker T past ε hε).toValuation φ = 0 := by
  have hnot : φ ∉ (MarketMaker T past ε hε).support :=
    fun hmem => hφ (MarketMaker_support T past ε hε hmem)
  rw [RationalBeliefState.toValuation,
    RationalBeliefState.quote_eq_zero_of_not_mem _ hnot]
  norm_num

lemma MarketMaker_worldValue_le {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) (ε : ℚ) (hε : 0 < ε)
    (b : ↥T.support → Bool) :
    T.value (Function.update (beliefHistory past) n
      (MarketMaker T past ε hε).toValuation) (supportBitWorld T b) ≤ (ε : ℝ) :=
  (MarketMaker_accepts T past ε hε).worldValue_le b

/-! ## Recursive MarketMaker history and `lem:mm` -/

namespace EF

/-- An expressible feature cannot distinguish histories which agree through a day above
its rank.  The environment form handles shared `letE` bindings without expanding them. -/
lemma denoteWith_eq_of_eqUpTo (e : EF) (ρ σ : List ℝ) (V W : History) (n : ℕ)
    (hrank : e.rank ≤ n)
    (hρ : ∀ i, ρ.getD i 0 = σ.getD i 0)
    (hVW : ∀ day, day ≤ n → ∀ φ, V day φ = W day φ) :
    e.denoteWith ρ V = e.denoteWith σ W := by
  induction e generalizing ρ σ with
  | price φ day =>
      exact hVW day hrank φ
  | const q => rfl
  | add a b iha ihb =>
      simp only [rank_add, max_le_iff] at hrank
      simp [denoteWith, iha ρ σ hrank.1 hρ, ihb ρ σ hrank.2 hρ]
  | mul a b iha ihb =>
      simp only [rank_mul, max_le_iff] at hrank
      simp [denoteWith, iha ρ σ hrank.1 hρ, ihb ρ σ hrank.2 hρ]
  | max a b iha ihb =>
      simp only [rank_max, max_le_iff] at hrank
      simp [denoteWith, iha ρ σ hrank.1 hρ, ihb ρ σ hrank.2 hρ]
  | safeRecip a iha =>
      simp [denoteWith, iha ρ σ hrank hρ]
  | var i =>
      exact hρ i
  | letE x body ihx ihbody =>
      simp only [rank_letE, max_le_iff] at hrank
      have hx := ihx ρ σ hrank.1 hρ
      simp only [denoteWith]
      apply ihbody (x.denoteWith ρ V :: ρ) (x.denoteWith σ W :: σ) hrank.2
      · intro i
        cases i with
        | zero => simpa using hx
        | succ i => simpa using hρ i

lemma denote_eq_of_eqUpTo (e : EF) (V W : History) (n : ℕ)
    (hrank : e.rank ≤ n)
    (hVW : ∀ day, day ≤ n → ∀ φ, V day φ = W day φ) :
    e.denote V = e.denote W := by
  exact e.denoteWith_eq_of_eqUpTo [] [] V W n hrank (by simp) hVW

end EF

namespace Strategy

/-- A legal day-`n` strategy only depends on prices through day `n`. -/
lemma value_eq_of_eqUpTo {n : ℕ} (T : Strategy n) (V W : History)
    (w : Sentence → ℝ) (hVW : ∀ day, day ≤ n → ∀ φ, V day φ = W day φ) :
    T.value V w = T.value W w := by
  unfold Strategy.value
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [p.1.denote_eq_of_eqUpTo V W n (T.rank_le p hp) hVW,
    hVW n le_rfl p.2]

/-- A payout table only matters on the strategy's syntactic support. -/
lemma value_eq_of_world_eqOn_support {n : ℕ} (T : Strategy n) (V : History)
    (w z : Sentence → ℝ) (hwz : ∀ φ ∈ T.support, w φ = z φ) :
    T.value V w = T.value V z := by
  rw [T.value_eq_sum_support, T.value_eq_sum_support]
  apply Finset.sum_congr rfl
  intro φ hφ
  rw [hwz φ hφ]

end Strategy

/-- The finite list of already-produced states supplied to MarketMaker on day `n`. -/
noncomputable def marketMakerPast (_Tr : Trader) (states : ℕ → RationalBeliefState)
    (n : ℕ) : List RationalBeliefState :=
  List.ofFn fun i : Fin n => states i

/-- Recursive sequence produced by applying MarketMaker to the trader's actual day strategy. -/
noncomputable def marketMakerStates (Tr : Trader) : ℕ → RationalBeliefState
  | n => MarketMaker (Tr.strat n)
      (List.ofFn fun i : Fin n => marketMakerStates Tr i)
      (marketMakerError n) (marketMakerError_pos n)
termination_by n => n
decreasing_by exact i.isLt

/-- The real market history generated recursively by MarketMaker. -/
noncomputable def marketMakerHistory (Tr : Trader) : History :=
  fun n => (marketMakerStates Tr n).toValuation

lemma beliefHistory_marketMakerPast {Tr : Trader} {n day : ℕ} (hday : day < n) :
    beliefHistory (marketMakerPast Tr (marketMakerStates Tr) n) day =
      marketMakerHistory Tr day := by
  funext φ
  simp [beliefHistory, rationalHistory, marketMakerPast, marketMakerHistory,
    RationalBeliefState.toValuation, hday]

lemma candidate_marketMakerHistory_eq_upTo (Tr : Trader) (n day : ℕ)
    (hday : day ≤ n) :
    Function.update
      (beliefHistory (marketMakerPast Tr (marketMakerStates Tr) n)) n
      (marketMakerStates Tr n).toValuation day = marketMakerHistory Tr day := by
  by_cases hdn : day = n
  · subst day
    simp [marketMakerHistory]
  · have hlt : day < n := lt_of_le_of_ne hday hdn
    simp [Function.update, hdn, beliefHistory_marketMakerPast hlt]

lemma supportBitWorld_pcWorld_eq {n : ℕ} (T : Strategy n) (v : PCWorld)
    (φ : Sentence) (hφ : φ ∈ T.support) :
    supportBitWorld T (fun ψ => decide (v.Holds ψ)) φ = v.payout φ := by
  by_cases hv : v.Holds φ <;> simp [supportBitWorld, PCWorld.payout, hφ, hv]

/-- One-day MarketMaker bound against every propositionally consistent world. -/
lemma marketMaker_day_value_le (Tr : Trader) (n : ℕ) (v : PCWorld) :
    (Tr.strat n).value (marketMakerHistory Tr) v.payout ≤
      (marketMakerError n : ℝ) := by
  let past := marketMakerPast Tr (marketMakerStates Tr) n
  let b : ↥(Tr.strat n).support → Bool := fun ψ => decide (v.Holds ψ)
  have hmm := MarketMaker_worldValue_le (Tr.strat n) past
    (marketMakerError n) (marketMakerError_pos n) b
  have hstate : MarketMaker (Tr.strat n) past (marketMakerError n)
      (marketMakerError_pos n) = marketMakerStates Tr n := by
    rw [marketMakerStates]
    rfl
  rw [hstate] at hmm
  have hworld : (Tr.strat n).value
      (Function.update (beliefHistory past) n (marketMakerStates Tr n).toValuation)
      (supportBitWorld (Tr.strat n) b) =
      (Tr.strat n).value
        (Function.update (beliefHistory past) n (marketMakerStates Tr n).toValuation)
        v.payout := by
    apply (Tr.strat n).value_eq_of_world_eqOn_support
    intro φ hφ
    exact supportBitWorld_pcWorld_eq (Tr.strat n) v φ hφ
  rw [hworld] at hmm
  have hhistory : (Tr.strat n).value
      (Function.update (beliefHistory past) n (marketMakerStates Tr n).toValuation)
      v.payout = (Tr.strat n).value (marketMakerHistory Tr) v.payout := by
    apply (Tr.strat n).value_eq_of_eqUpTo
    intro day hday φ
    exact congrFun (candidate_marketMakerHistory_eq_upTo Tr n day hday) φ
  rw [hhistory] at hmm
  exact hmm

lemma marketMakerError_cast (n : ℕ) :
    (marketMakerError n : ℝ) = (1 / 2 : ℝ) ^ (n + 1) := by
  norm_num [marketMakerError, div_pow]

lemma sum_marketMakerError (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (marketMakerError i : ℝ) =
      1 - (1 / 2 : ℝ) ^ (n + 1) := by
  induction n with
  | zero => norm_num [marketMakerError]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, marketMakerError_cast]
      rw [pow_succ]
      ring

lemma sum_marketMakerError_lt_one (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (marketMakerError i : ℝ) < 1 := by
  rw [sum_marketMakerError]
  have hpow : 0 < (1 / 2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
  linarith

/-- Every finite-horizon plausible assessment of the MarketMaker history is below one. -/
lemma marketMaker_netWorth_lt_one (Tr : Trader) (v : PCWorld) (n : ℕ) :
    Tr.netWorth (marketMakerHistory Tr) v n < 1 := by
  unfold Trader.netWorth
  calc
    ∑ i ∈ Finset.range (n + 1),
        (Tr.strat i).value (marketMakerHistory Tr) v.payout ≤
        ∑ i ∈ Finset.range (n + 1), (marketMakerError i : ℝ) := by
          exact Finset.sum_le_sum (fun i _ => marketMaker_day_value_le Tr i v)
    _ < 1 := sum_marketMakerError_lt_one n

/-- **MarketMaker lemma** (`lem:mm`).  The recursively generated rational market is not
exploited by the trader it faces, for any deductive process: all of the trader's plausible
assessments are uniformly bounded above by the geometric error budget `1`. -/
theorem marketMaker_not_exploited (Tr : Trader) (DP : DeductiveProcess) :
    ¬ Tr.Exploits (marketMakerHistory Tr) DP := by
  intro hexploits
  apply hexploits.2
  refine ⟨1, ?_⟩
  rintro x ⟨n, v, _hconsistent, rfl⟩
  exact (marketMaker_netWorth_lt_one Tr v n).le

/-- **Fixed Point Lemma** (`lem:fpl`).  For an actual finite day-`n` strategy and an
arbitrary prior history, there is a `[0,1]` valuation supported on the sentences traded by
the strategy such that the resulting one-day position has nonpositive value in every
propositionally consistent world.

The strategy syntax may repeat a sentence.  The proof applies Brouwer to the aggregate
share demand for that sentence, matching the paper's coefficient notation `T[φ]`. -/
theorem fixed_point_lemma {n : ℕ} (T : Strategy n) (prior : History) :
    ∃ V : Valuation,
      (∀ φ, 0 ≤ V φ ∧ V φ ≤ 1) ∧
      (∀ φ, φ ∉ T.support → V φ = 0) ∧
      ∀ v : PCWorld, T.value (Function.update prior n V) v.payout ≤ 0 := by
  obtain ⟨V, hV, hsupp, hvalue⟩ := fixed_point_lemma_bounded T prior
  refine ⟨V, hV, hsupp, fun v => hvalue v.payout ?_⟩
  intro φ
  by_cases hv : v.Holds φ <;> simp [PCWorld.payout, hv]

#print axioms fixed_point_lemma_bounded
#print axioms fixed_point_lemma
#print axioms MarketMaker_search_clock
#print axioms marketMaker_not_exploited

end LogicalInduction
