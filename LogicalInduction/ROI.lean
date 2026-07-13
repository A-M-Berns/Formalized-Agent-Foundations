/-
# Repeatable return on investment (`LogicalInduction.ROI`)

This file isolates the capital-allocation argument used by the paper's repeatable-ROI
lemma.  `open i n` records that the `i`th component trader is still tying up capital on
day `n`.  The recursively chosen weight is exactly the capital not tied up by earlier
components on that day.
-/
import LogicalInduction.Engine
import LogicalInduction.Computable
import Mathlib.Algebra.BigOperators.Fin

namespace LogicalInduction

open scoped BigOperators

/-! ## Uniformly emulatable trader families -/

/-- Operational form of the paper's efficiently emulatable sequence. A single uniform
token program emits member `k` on day `n` in a polynomial bound independent of `k` (for
`k ≤ n`), and member `k` is identically zero before day `k`. The paper phrases this as an
efficiently generated sequence of uniformly bounded programs; pairing `k` into the input
is the equivalent universal-program presentation used by our token emitter. -/
def EfficientlyEmulatable (Ts : ℕ → Trader) : Prop :=
  ∃ (code : Nat.Partrec.Code) (a d : ℕ),
    (∀ k n, n < k → ((Ts k).strat n).trades = []) ∧
    (∀ k n, k ≤ n →
      (serializeTrades ((Ts k).strat n).trades).length ≤ a * (n + 1) ^ d + a) ∧
    ∀ k n i, k ≤ n → i < (serializeTrades ((Ts k).strat n).trades).length →
      Nat.Partrec.Code.evaln (a * (n + 1) ^ d + a) code
          (Nat.pair k (Nat.pair n i)) =
        some ((serializeTrades ((Ts k).strat n).trades).getD i 0)

theorem EfficientlyEmulatable.zero_before {Ts : ℕ → Trader}
    (h : EfficientlyEmulatable Ts) {k n : ℕ} (hnk : n < k) :
    ((Ts k).strat n).trades = [] := by
  obtain ⟨_, _, _, hz, _, _⟩ := h
  exact hz k n hnk

theorem Trader.netWorth_succ (Tr : Trader) (V : History) (v : PCWorld) (n : ℕ) :
    Tr.netWorth V v (n + 1) =
      Tr.netWorth V v n + (Tr.strat (n + 1)).value V v.payout := by
  simp [Trader.netWorth, Finset.sum_range_succ]

/-- A family member contributes no pre-launch value, so its net worth on launch day is
exactly that day's strategy value. -/
theorem EfficientlyEmulatable.netWorth_launch {Ts : ℕ → Trader}
    (h : EfficientlyEmulatable Ts) (V : History) (v : PCWorld) (k : ℕ) :
    (Ts k).netWorth V v k = ((Ts k).strat k).value V v.payout := by
  rw [Trader.netWorth]
  apply Finset.sum_eq_single k
  · intro i hi hik
    have hil : i < k := by
      simp only [Finset.mem_range] at hi
      omega
    rw [Strategy.value]
    rw [show ((Ts k).strat i).trades = [] from h.zero_before hil]
    simp [Strategy.value]
  · intro hk
    simp at hk

/-- Structured operational witness for an emulatable trader family. The raw
`EfficientlyEmulatable` program certifies the paper-facing token semantics; these extra
fields expose polynomially computable trade boundaries, coefficient segments, and sentence
codes. That boundary data is exactly what a uniform syntax transformation (such as scaling
every trade by a generated feature) needs. Indices are
`z = ⟨⟨k,n⟩,j⟩`: family member, day, then trade number. -/
structure PolyTradeEmulatable (Ts : ℕ → Trader) where
  emulatable : EfficientlyEmulatable Ts
  tradeCount : ℕ → ℕ
  coefficient : ℕ → EF
  sentence : ℕ → Sentence
  tradeCount_poly : ∃ c, PolyFueled c tradeCount
  coefficient_poly : PolySegStream (fun z => (coefficient z).serialize)
  sentence_poly : ∃ c, PolyFueled c (fun z => Encodable.encode (sentence z))
  trades_eq : ∀ k n,
    ((Ts k).strat n).trades =
      (List.range (tradeCount (Nat.pair k n))).map (fun j =>
        let z := Nat.pair (Nat.pair k n) j
        (coefficient z, sentence z))

@[simp] theorem serializeTrades_append (xs ys : List (EF × Sentence)) :
    serializeTrades (xs ++ ys) = serializeTrades xs ++ serializeTrades ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, serializeTrades, ih, List.append_assoc]

theorem serializeTrades_flatMap {α : Type} (xs : List α) (f : α → List (EF × Sentence)) :
    serializeTrades (xs.flatMap f) = xs.flatMap (fun x => serializeTrades (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem serializeTrades_map_singleton {α : Type} (xs : List α)
    (f : α → EF × Sentence) :
    serializeTrades (xs.map f) = xs.flatMap (fun x => serializeTrades [f x]) := by
  rw [← serializeTrades_flatMap]
  congr 1
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- The structured witness gives a compositional segment emitter for each component/day
trade list. This is the reusable bridge from trade-level boundary data back to the faithful
`serializeTrades` representation. -/
theorem PolyTradeEmulatable.polySeg {Ts : ℕ → Trader} (h : PolyTradeEmulatable Ts) :
    PolySegStream (fun z =>
      serializeTrades ((Ts z.unpair.1).strat z.unpair.2).trades) := by
  obtain ⟨ccount, hcount⟩ := h.tradeCount_poly
  obtain ⟨csentence, hsentence⟩ := h.sentence_poly
  have htag : PolySegStream (fun _ => [6]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 6)
  have hsentenceSeg : PolySegStream (fun z => [Encodable.encode (h.sentence z)]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.polyTok hsentence)
  have hone : PolySegStream (fun z =>
      serializeTrades [(h.coefficient z, h.sentence z)]) := by
    refine PolySegStream.of_eq
      ((h.coefficient_poly.append htag).append hsentenceSeg) ?_
    intro z
    simp [serializeTrades, List.append_assoc]
  have hall := PolySegStream.concatVar hone hcount
  refine PolySegStream.of_eq hall ?_
  intro z
  rw [h.trades_eq]
  rw [serializeTrades_map_singleton]
  simp only [Nat.pair_unpair]

namespace Strategy

/-- Multiply every share coefficient in a strategy by one legal feature. -/
def scaleBy {n : ℕ} (e : EF) (he : e.rank ≤ n) (T : Strategy n) : Strategy n where
  trades := T.trades.map (fun p => (EF.mul e p.1, p.2))
  rank_le := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact Nat.max_le.mpr ⟨he, T.rank_le q hq⟩

theorem scaleBy_value {n : ℕ} (e : EF) (he : e.rank ≤ n) (T : Strategy n)
    (V : History) (w : Valuation) :
    (T.scaleBy e he).value V w = e.denote V * T.value V w := by
  simp only [scaleBy, Strategy.value, List.map_map]
  induction T.trades with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply, EF.denote_mul,
        Pi.mul_apply] at ih ⊢
      rw [ih]
      ring

theorem scaleBy_magnitude {n : ℕ} (e : EF) (he : e.rank ≤ n) (T : Strategy n)
    (V : History) :
    (T.scaleBy e he).magnitude V = |e.denote V| * T.magnitude V := by
  simp only [scaleBy, Strategy.magnitude, List.map_map]
  induction T.trades with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply, EF.denote_mul,
        Pi.mul_apply, abs_mul] at ih ⊢
      rw [ih]
      ring

/-- Concatenate a finite collection of same-day strategies. -/
def join {n : ℕ} (ts : List (Strategy n)) : Strategy n where
  trades := ts.flatMap Strategy.trades
  rank_le := by
    intro p hp
    simp only [List.mem_flatMap] at hp
    obtain ⟨T, hT, hp⟩ := hp
    exact T.rank_le p hp

theorem join_value {n : ℕ} (ts : List (Strategy n)) (V : History) (w : Valuation) :
    (Strategy.join ts).value V w = (ts.map (fun T => T.value V w)).sum := by
  induction ts with
  | nil => simp [join, Strategy.value]
  | cons T ts ih =>
      calc
        (Strategy.join (T :: ts)).value V w =
            T.value V w + (Strategy.join ts).value V w := by
              simp [Strategy.join, Strategy.value]
        _ = ((T :: ts).map (fun S => S.value V w)).sum := by
              rw [ih]
              rfl

theorem join_magnitude {n : ℕ} (ts : List (Strategy n)) (V : History) :
    (Strategy.join ts).magnitude V = (ts.map (fun T => T.magnitude V)).sum := by
  induction ts with
  | nil => simp [join, Strategy.magnitude]
  | cons T ts ih =>
      calc
        (Strategy.join (T :: ts)).magnitude V =
            T.magnitude V + (Strategy.join ts).magnitude V := by
              simp [Strategy.join, Strategy.magnitude]
        _ = ((T :: ts).map (fun S => S.magnitude V)).sum := by
              rw [ih]
              rfl

end Strategy

namespace ROIBudget

/-- The openness table is efficiently available to the syntax emitter. Inputs are paired
as `⟨k,i⟩`; output `1` means component `i` is active at budget stage `k`. -/
def PolyActiveSchedule (active : ℕ → ℕ → Bool) : Prop :=
  ∃ c : Nat.Partrec.Code, PolyFueled c (fun z => if active z.unpair.2 z.unpair.1 then 1 else 0)

/-- Sum a finite list of expressible features inside the feature DSL. -/
def sumFeatures : List EF → EF :=
  List.foldr EF.add (EF.const 0)

theorem serialize_sumFeatures (es : List EF) :
    (sumFeatures es).serialize = es.flatMap EF.serialize ++
      (EF.const 0).serialize ++ List.replicate es.length 2 := by
  induction es with
  | nil => simp [sumFeatures, EF.serialize]
  | cons e es ih =>
      change e.serialize ++ (sumFeatures es).serialize ++ [2] = _
      rw [ih]
      simp only [List.flatMap_cons, List.length_cons]
      rw [List.replicate_succ']
      simp only [List.append_assoc]

theorem sumFeatures_denote (es : List EF) (V : History) :
    (sumFeatures es).denote V = (es.map (fun e => e.denote V)).sum := by
  induction es with
  | nil => simp [sumFeatures]
  | cons e es ih =>
      change e.denote V + (sumFeatures es).denote V =
        e.denote V + (es.map (fun e => e.denote V)).sum
      rw [ih]

theorem sumFeatures_denoteWith (es : List EF) (ρ : List ℝ) (V : History) :
    (sumFeatures es).denoteWith ρ V =
      (es.map (fun e => e.denoteWith ρ V)).sum := by
  induction es with
  | nil => simp [sumFeatures, EF.denoteWith]
  | cons e es ih =>
      change e.denoteWith ρ V + (sumFeatures es).denoteWith ρ V =
        e.denoteWith ρ V + (es.map (fun e => e.denoteWith ρ V)).sum
      rw [ih]

theorem sumFeatures_rank_le (es : List EF) (n : ℕ)
    (h : ∀ e ∈ es, e.rank ≤ n) : (sumFeatures es).rank ≤ n := by
  induction es with
  | nil => change 0 ≤ n; omega
  | cons e es ih =>
      change Nat.max e.rank (sumFeatures es).rank ≤ n
      exact Nat.max_le.mpr ⟨h e (by simp), ih (fun x hx => h x (by simp [hx]))⟩

theorem sumFeatures_rankWith_le (es : List EF) (ρ : List ℕ) (n : ℕ)
    (h : ∀ e ∈ es, e.rankWith ρ ≤ n) : (sumFeatures es).rankWith ρ ≤ n := by
  induction es with
  | nil => change 0 ≤ n; omega
  | cons e es ih =>
      change Nat.max (e.rankWith ρ) ((sumFeatures es).rankWith ρ) ≤ n
      exact Nat.max_le.mpr ⟨h e (by simp), ih (fun x hx => h x (by simp [hx]))⟩

/-- Capital currently tied up by components with index below `n`. -/
noncomputable def outstanding (active : ℕ → ℕ → Bool) (α β : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin n, if active i n then β i * α i else 0

/-- The paper's adaptive scaling coefficient
`βₙ = 1 - ∑_{i<n, open(i,n)} βᵢ αᵢ`.

Well-founded recursion is appropriate here: the right hand side only asks for weights
with index strictly below `n`. -/
noncomputable def weight (active : ℕ → ℕ → Bool) (α : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 - ∑ i : Fin n,
    if active i n then weight active α i * α i else 0
termination_by n
decreasing_by exact i.isLt

/-- The budget coefficient reified as an expressible feature. Each openness bit is
precomputed by the slow maturity search and inserted as syntax, exactly as in the paper. -/
def featureWeight (active : ℕ → ℕ → Bool) (α : ℕ → EF) (n : ℕ) : EF :=
  EF.add (EF.const 1) (EF.mul (EF.const (-1))
    (sumFeatures (List.ofFn (fun i : Fin n =>
      if active i n then EF.mul (featureWeight active α i) (α i) else EF.const 0))))
termination_by n
decreasing_by exact i.isLt

/-- Syntactic budget coefficients denote the semantic adaptive weights. -/
theorem featureWeight_denote (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (V : History) (n : ℕ) :
    (featureWeight active α n).denote V =
      weight active (fun i => (α i).denote V) n := by
  rw [featureWeight, weight]
  simp only [EF.denote_add, EF.denote_const, EF.denote_mul, Pi.add_apply, Pi.mul_apply,
    Rat.cast_one, Rat.cast_neg, neg_mul, one_mul]
  rw [sumFeatures_denote]
  simp only [List.map_ofFn, List.sum_ofFn]
  apply congrArg (fun x : ℝ => 1 - x)
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : active i n = true
  · simp only [Function.comp_apply, h, if_true, EF.denote_mul, Pi.mul_apply]
    rw [featureWeight_denote]
  · simp [Function.comp_apply, h]

/-- If the magnitude progression is rank-respecting, so is every reified budget
coefficient. Thus `βₙ†` is legal to use on every day `m ≥ n`. -/
theorem featureWeight_rank_le (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hα : ∀ i, (α i).rank ≤ i) : ∀ n, (featureWeight active α n).rank ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [featureWeight]
      simp only [EF.rank_add, EF.rank_const, EF.rank_mul]
      apply Nat.max_le.mpr
      constructor
      · omega
      · apply Nat.max_le.mpr
        constructor
        · omega
        · apply sumFeatures_rank_le
          intro e he
          simp only [List.mem_ofFn] at he
          obtain ⟨i, rfl⟩ := he
          split
          · exact Nat.max_le.mpr ⟨(ih i i.isLt).trans (Nat.le_of_lt i.isLt),
              (hα i).trans (Nat.le_of_lt i.isLt)⟩
          · change 0 ≤ n
            omega

/-! ### Shared straight-line budget expression -/

/-- The right-hand side defining `βₖ`, interpreted in an environment containing
`[βₖ₋₁, …, β₀]`. -/
def featureWeightBody (active : ℕ → ℕ → Bool) (α : ℕ → EF) (k : ℕ) : EF :=
  EF.add (EF.const 1) (EF.mul (EF.const (-1))
    (sumFeatures (List.ofFn (fun i : Fin k =>
      if active i k then EF.mul (EF.var (k - 1 - i)) (α i) else EF.const 0))))

/-- Uniform variable-length emission of the recurrence bodies. This is the triangular
`i < k` use of `PolySegStream.concatVar`: each term conditionally emits either
`var(k-1-i) * αᵢ` or zero, and the fold's postfix `add` tags form a second linear run. -/
theorem featureWeightBody_polySeg (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hα : PolySegStream (fun i => (α i).serialize))
    (hactive : PolyActiveSchedule active) :
    PolySegStream (fun k => (featureWeightBody active α k).serialize) := by
  obtain ⟨cactive, hactivePF⟩ := hactive
  let term : ℕ → EF := fun z =>
    if active z.unpair.2 z.unpair.1 then
      EF.mul (EF.var (z.unpair.1 - 1 - z.unpair.2)) (α z.unpair.2)
    else EF.const 0
  have idxPF := subc_polyFueled.comp
    ((predc_polyFueled.comp PolyFueled.left).pair PolyFueled.right)
  have idxPF' := idxPF.of_eq (f' := fun z => z.unpair.1 - 1 - z.unpair.2)
    (fun z => by simp [Nat.pred_eq_sub_one])
  have hvar : PolySegStream
      (fun z => (EF.var (z.unpair.1 - 1 - z.unpair.2)).serialize) :=
    PolySegStream.serialize_var idxPF'
  have hαright : PolySegStream (fun z => (α z.unpair.2).serialize) :=
    hα.comp PolyFueled.right
  have hmul : PolySegStream (fun z =>
      (EF.mul (EF.var (z.unpair.1 - 1 - z.unpair.2)) (α z.unpair.2)).serialize) :=
    PolySegStream.serialize_mul hvar hαright
  have hzero : PolySegStream (fun _ => (EF.const 0).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0)
  have hterm : PolySegStream (fun z => (term z).serialize) := by
    have hchoose := PolySegStream.ifZero hzero hmul hactivePF
    refine PolySegStream.of_eq hchoose ?_
    intro z
    simp only [term]
    by_cases h : active z.unpair.2 z.unpair.1 = true
    · simp [h]
    · have hf : active z.unpair.2 z.unpair.1 = false := Bool.eq_false_of_not_eq_true h
      simp [hf]
  have hterms : PolySegStream (fun k =>
      (List.range k).flatMap (fun i => (term (Nat.pair k i)).serialize)) :=
    PolySegStream.concatVar hterm PolyFueled.id
  have haddTags : PolySegStream (fun k => List.replicate k 2) :=
    PolySegStream.repeatTag 2 PolyFueled.id
  have hsumRaw := (hterms.append hzero).append haddTags
  have hsum : PolySegStream (fun k =>
      (sumFeatures (List.ofFn (fun i : Fin k => term (Nat.pair k i)))).serialize) := by
    refine PolySegStream.of_eq hsumRaw ?_
    intro k
    rw [serialize_sumFeatures]
    simp only [List.length_ofFn]
    congr 2
    rw [← List.map_coe_finRange_eq_range]
    rw [List.flatMap_map]
    simp only [List.ofFn_eq_map, List.flatMap_map]
  have hone : PolySegStream (fun _ => (EF.const 1).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 1)
  have hnegone : PolySegStream (fun _ => (EF.const (-1)).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))
  have hbody := PolySegStream.serialize_add hone
    (PolySegStream.serialize_mul hnegone hsum)
  refine PolySegStream.of_eq hbody ?_
  intro k
  simp only [featureWeightBody, term]
  congr 4
  congr 1
  funext i
  simp

/-- Bind `count` consecutive budget variables starting at `k`, then return the last one.
Each earlier `β` is represented once and referenced by a constant-size `EF.var`. -/
def sharedWeights (active : ℕ → ℕ → Bool) (α : ℕ → EF) (k : ℕ) : ℕ → EF
  | 0 => EF.var 0
  | count + 1 => EF.letE (featureWeightBody active α k)
      (sharedWeights active α (k + 1) count)

/-- Polynomial-sharing version of the day-`n` budget coefficient. -/
def sharedFeatureWeight (active : ℕ → ℕ → Bool) (α : ℕ → EF) (n : ℕ) : EF :=
  sharedWeights active α 0 (n + 1)

/-- The postfix stream of a shared chain consists of its consecutive binding bodies,
the terminal reference to the newest binding, and one `letE` tag per binding. -/
theorem sharedWeights_serialize (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (k count : ℕ) :
    (sharedWeights active α k count).serialize =
      (List.range' k count).flatMap
          (fun j => (featureWeightBody active α j).serialize) ++
        (EF.var 0).serialize ++ List.replicate count 8 := by
  induction count generalizing k with
  | zero => simp [sharedWeights, EF.serialize]
  | succ count ih =>
      rw [sharedWeights]
      change (featureWeightBody active α k).serialize ++
          (sharedWeights active α (k + 1) count).serialize ++ [8] = _
      rw [ih (k + 1)]
      simp [List.range'_succ, List.replicate_succ', List.append_assoc]

/-- Uniform polynomial-time emission of the complete shared coefficient `βₙ†`.
This is the representation-level closure needed in addition to its semantic, rank,
and exact-cost specifications below. -/
theorem sharedFeatureWeight_polySeg (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hα : PolySegStream (fun i => (α i).serialize))
    (hactive : PolyActiveSchedule active) :
    PolySegStream (fun n => (sharedFeatureWeight active α n).serialize) := by
  have hbody := featureWeightBody_polySeg active α hα hactive
  have hbodies : PolySegStream (fun n =>
      (List.range (n + 1)).flatMap
        (fun j => (featureWeightBody active α j).serialize)) := by
    refine PolySegStream.of_eq
      (PolySegStream.concatVar (hbody.comp PolyFueled.right)
        PolyFueled.id.succ_comp) ?_
    intro n
    simp only [Nat.unpair_pair]
  have hvar : PolySegStream (fun _ => (EF.var 0).serialize) :=
    PolySegStream.serialize_var (PolyFueled.const 0)
  have htags : PolySegStream (fun n => List.replicate (n + 1) 8) :=
    PolySegStream.repeatTag 8 PolyFueled.id.succ_comp
  refine PolySegStream.of_eq ((hbodies.append hvar).append htags) ?_
  intro n
  rw [sharedFeatureWeight, sharedWeights_serialize]
  rw [List.range_eq_range']

/-- Exact non-duplicating cost recurrence for the shared representation. Earlier budget
expressions contribute only a variable reference in later bodies. -/
def sharedWeightCost (active : ℕ → ℕ → Bool) (α : ℕ → EF) (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | count + 1 => (featureWeightBody active α k).cost +
      sharedWeightCost active α (k + 1) count + 1

theorem sharedWeights_cost_eq (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (k count : ℕ) :
    (sharedWeights active α k count).cost = sharedWeightCost active α k count := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih =>
      simp only [sharedWeights, sharedWeightCost, EF.cost]
      rw [ih]

theorem sharedFeatureWeight_cost_eq (active : ℕ → ℕ → Bool) (α : ℕ → EF) (n : ℕ) :
    (sharedFeatureWeight active α n).cost = sharedWeightCost active α 0 (n + 1) := by
  exact sharedWeights_cost_eq active α 0 (n + 1)

private def PriorWeightEnv (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (V : History) (k : ℕ) (ρ : List ℝ) : Prop :=
  ∀ i : Fin k, ρ.getD (k - 1 - i) 0 = weight active (fun j => (α j).denote V) i

private theorem featureWeightBody_denoteWith (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hαc : ∀ i ρ V, (α i).denoteWith ρ V = (α i).denote V)
    (V : History) (k : ℕ) (ρ : List ℝ) (hρ : PriorWeightEnv active α V k ρ) :
    (featureWeightBody active α k).denoteWith ρ V =
      weight active (fun j => (α j).denote V) k := by
  rw [featureWeightBody, weight]
  simp only [EF.denoteWith, Rat.cast_one, Rat.cast_neg, neg_mul, one_mul]
  have hsum :
      (sumFeatures (List.ofFn (fun i : Fin k =>
        if active i k then EF.mul (EF.var (k - 1 - i)) (α i) else EF.const 0))).denoteWith ρ V =
      ∑ i : Fin k, if active i k then
        weight active (fun j => (α j).denote V) i * (α i).denote V else 0 := by
    rw [sumFeatures_denoteWith]
    simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hop : active i k = true
    · simp only [hop, if_true, EF.denoteWith]
      rw [hρ i]
      rw [hαc i ρ V]
    · simp [hop, EF.denoteWith]
  rw [hsum]
  ring

private theorem priorWeightEnv_cons (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (V : History) (k : ℕ) (ρ : List ℝ) (hρ : PriorWeightEnv active α V k ρ) :
    PriorWeightEnv active α V (k + 1)
      (weight active (fun j => (α j).denote V) k :: ρ) := by
  intro i
  by_cases hi : (i : ℕ) = k
  · have hilast : i = Fin.last k := Fin.ext hi
    subst i
    simp
  · have hik : (i : ℕ) < k := by omega
    have hidx : k + 1 - 1 - (i : ℕ) = (k - 1 - (i : ℕ)) + 1 := by omega
    rw [hidx]
    simp only [List.getD_cons_succ]
    exact hρ ⟨i, hik⟩

private theorem sharedWeights_denoteWith (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hαc : ∀ i ρ V, (α i).denoteWith ρ V = (α i).denote V)
    (V : History) (k count : ℕ) (ρ : List ℝ) (hρ : PriorWeightEnv active α V k ρ) :
    (sharedWeights active α k count).denoteWith ρ V =
      if count = 0 then ρ.getD 0 0
      else weight active (fun j => (α j).denote V) (k + count - 1) := by
  induction count generalizing k ρ with
  | zero => simp [sharedWeights, EF.denoteWith]
  | succ count ih =>
      rw [sharedWeights, EF.denoteWith,
        featureWeightBody_denoteWith active α hαc V k ρ hρ]
      rw [ih (k := k + 1)
        (ρ := weight active (fun j => (α j).denote V) k :: ρ)
        (priorWeightEnv_cons active α V k ρ hρ)]
      cases count with
      | zero => simp
      | succ count =>
          simp
          congr 1
          omega

/-- The shared straight-line expression denotes exactly the same adaptive coefficient as
the semantic recurrence. -/
theorem sharedFeatureWeight_denote (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hαc : ∀ i ρ V, (α i).denoteWith ρ V = (α i).denote V)
    (V : History) (n : ℕ) :
    (sharedFeatureWeight active α n).denote V =
      weight active (fun i => (α i).denote V) n := by
  rw [sharedFeatureWeight, EF.denote]
  simpa using sharedWeights_denoteWith active α hαc V 0 (n + 1) [] (by
    intro i
    exact Fin.elim0 i)

private def PriorRankEnv (k : ℕ) (ρ : List ℕ) : Prop :=
  ∀ i : Fin k, ρ.getD (k - 1 - i) 0 ≤ i

private theorem featureWeightBody_rankWith_le (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hα : ∀ i, (α i).rank ≤ i) (hαr : ∀ i ρ, (α i).rankWith ρ = (α i).rank)
    (k : ℕ) (ρ : List ℕ)
    (hρ : PriorRankEnv k ρ) : (featureWeightBody active α k).rankWith ρ ≤ k := by
  rw [featureWeightBody]
  simp only [EF.rankWith]
  apply Nat.max_le.mpr
  constructor
  · omega
  · apply Nat.max_le.mpr
    constructor
    · omega
    · apply sumFeatures_rankWith_le
      intro e he
      simp only [List.mem_ofFn] at he
      obtain ⟨i, rfl⟩ := he
      split
      · exact Nat.max_le.mpr ⟨(hρ i).trans (Nat.le_of_lt i.isLt),
          (by rw [hαr i ρ]; exact (hα i).trans (Nat.le_of_lt i.isLt))⟩
      · change 0 ≤ k
        omega

private theorem priorRankEnv_cons (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hα : ∀ i, (α i).rank ≤ i) (hαr : ∀ i ρ, (α i).rankWith ρ = (α i).rank)
    (k : ℕ) (ρ : List ℕ) (hρ : PriorRankEnv k ρ) :
    PriorRankEnv (k + 1) ((featureWeightBody active α k).rankWith ρ :: ρ) := by
  intro i
  by_cases hi : (i : ℕ) = k
  · have hilast : i = Fin.last k := Fin.ext hi
    subst i
    simpa using featureWeightBody_rankWith_le active α hα hαr k ρ hρ
  · have hik : (i : ℕ) < k := by omega
    have hidx : k + 1 - 1 - (i : ℕ) = (k - 1 - (i : ℕ)) + 1 := by omega
    rw [hidx]
    simp only [List.getD_cons_succ]
    exact hρ ⟨i, hik⟩

private theorem sharedWeights_rankWith_le (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hα : ∀ i, (α i).rank ≤ i) (hαr : ∀ i ρ, (α i).rankWith ρ = (α i).rank)
    (k count : ℕ) (ρ : List ℕ)
    (hρ : PriorRankEnv k ρ) :
    (sharedWeights active α k count).rankWith ρ ≤
      if count = 0 then ρ.getD 0 0 else k + count - 1 := by
  induction count generalizing k ρ with
  | zero => simp [sharedWeights, EF.rankWith]
  | succ count ih =>
      rw [sharedWeights, EF.rankWith]
      have H := ih (k := k + 1)
        (ρ := (featureWeightBody active α k).rankWith ρ :: ρ)
        (priorRankEnv_cons active α hα hαr k ρ hρ)
      cases count with
      | zero =>
          exact H.trans (featureWeightBody_rankWith_le active α hα hαr k ρ hρ)
      | succ count =>
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using H

private theorem featureWeightBody_rank_le (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hα : ∀ i, (α i).rank ≤ i) (k : ℕ) :
    (featureWeightBody active α k).rank ≤ k := by
  rw [featureWeightBody]
  simp only [EF.rank]
  apply Nat.max_le.mpr
  constructor
  · omega
  · apply Nat.max_le.mpr
    constructor
    · omega
    · apply sumFeatures_rank_le
      intro e he
      simp only [List.mem_ofFn] at he
      obtain ⟨i, rfl⟩ := he
      split
      · exact Nat.max_le.mpr ⟨by simp, (hα i).trans (Nat.le_of_lt i.isLt)⟩
      · simpa using Nat.zero_le k

private theorem sharedWeights_rank_le (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hα : ∀ i, (α i).rank ≤ i) (k count : ℕ) :
    (sharedWeights active α k count).rank ≤
      if count = 0 then 0 else k + count - 1 := by
  induction count generalizing k with
  | zero => simp [sharedWeights, EF.rank]
  | succ count ih =>
      rw [sharedWeights, EF.rank]
      apply Nat.max_le.mpr
      constructor
      · exact (featureWeightBody_rank_le active α hα k).trans (by
          cases count <;> simp <;> omega)
      · have H := ih (k + 1)
        cases count with
        | zero => simpa [sharedWeights, EF.rank] using H
        | succ count =>
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using H

theorem sharedFeatureWeight_rank_le (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hα : ∀ i, (α i).rank ≤ i) (n : ℕ) :
    (sharedFeatureWeight active α n).rank ≤ n := by
  rw [sharedFeatureWeight]
  simpa using sharedWeights_rank_le active α hα 0 (n + 1)

/-- Budgeted component sum using the shared straight-line `β` representation. -/
def sharedBudgetedTrader (Ts : ℕ → Trader) (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hα : ∀ i, (α i).rank ≤ i) : Trader where
  strat n := Strategy.join (List.ofFn (fun i : Fin (n + 1) =>
    Strategy.scaleBy (sharedFeatureWeight active α i)
      ((sharedFeatureWeight_rank_le active α hα i).trans (by omega))
      ((Ts i).strat n)))

/-- The shared budget construction preserves uniform segment emission for a structured
emulatable family. The proof performs two variable-width concatenations: trades within one
component, then all components launched by day `n`. -/
theorem sharedBudgetedTrader_polySeg (Ts : ℕ → Trader)
    (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hαrank : ∀ i, (α i).rank ≤ i)
    (hαseg : PolySegStream (fun i => (α i).serialize))
    (hactive : PolyActiveSchedule active)
    (hTs : PolyTradeEmulatable Ts) :
    PolySegStream (fun n =>
      serializeTrades ((sharedBudgetedTrader Ts active α hαrank).strat n).trades) := by
  obtain ⟨ccount, hcount⟩ := hTs.tradeCount_poly
  obtain ⟨csentence, hsentence⟩ := hTs.sentence_poly
  -- Input to an individual scaled trade is `q = ⟨⟨n,k⟩,j⟩`.
  have hday := PolyFueled.left.comp PolyFueled.left
  have hmember := PolyFueled.right.comp PolyFueled.left
  have htradeNo := PolyFueled.right
  have hcanonical := (hmember.pair hday).pair htradeNo
  have hβ := (sharedFeatureWeight_polySeg active α hαseg hactive).comp hmember
  have hcoeff := hTs.coefficient_poly.comp hcanonical
  have hscaled := PolySegStream.serialize_mul hβ hcoeff
  have htag : PolySegStream (fun _ => [6]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 6)
  have hsentenceSeg : PolySegStream (fun q =>
      [Encodable.encode (hTs.sentence
        (Nat.pair (Nat.pair q.unpair.1.unpair.2 q.unpair.1.unpair.1) q.unpair.2))]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.polyTok (hsentence.comp hcanonical))
  have hone : PolySegStream (fun q =>
      let n := q.unpair.1.unpair.1
      let k := q.unpair.1.unpair.2
      let j := q.unpair.2
      let z := Nat.pair (Nat.pair k n) j
      serializeTrades [
        (EF.mul (sharedFeatureWeight active α k) (hTs.coefficient z), hTs.sentence z)]) := by
    refine PolySegStream.of_eq ((hscaled.append htag).append hsentenceSeg) ?_
    intro q
    simp [serializeTrades, List.append_assoc]
  have hcountReindexed := hcount.comp (PolyFueled.right.pair PolyFueled.left)
  have hcomponent := PolySegStream.concatVar hone hcountReindexed
  have hall := PolySegStream.concatVar hcomponent PolyFueled.id.succ_comp
  refine PolySegStream.of_eq hall ?_
  intro n
  rw [sharedBudgetedTrader]
  simp only [Strategy.join, Strategy.scaleBy]
  rw [serializeTrades_flatMap]
  simp only [List.ofFn_eq_map]
  rw [← List.map_coe_finRange_eq_range]
  rw [List.flatMap_map]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro k hk
  simp only [Nat.unpair_pair]
  rw [hTs.trades_eq]
  rw [List.map_map]
  rw [serializeTrades_map_singleton]
  simp only [Function.comp_apply]

theorem sharedBudgetedTrader_ecTok (Ts : ℕ → Trader)
    (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hαrank : ∀ i, (α i).rank ≤ i)
    (hαseg : PolySegStream (fun i => (α i).serialize))
    (hactive : PolyActiveSchedule active)
    (hTs : PolyTradeEmulatable Ts) :
    EfficientlyComputableTok (sharedBudgetedTrader Ts active α hαrank) :=
  ecTok_of_segStream _
    (sharedBudgetedTrader_polySeg Ts active α hαrank hαseg hactive hTs)

theorem sharedBudgetedTrader_value (Ts : ℕ → Trader) (active : ℕ → ℕ → Bool)
    (α : ℕ → EF) (hα : ∀ i, (α i).rank ≤ i)
    (hαc : ∀ i ρ V, (α i).denoteWith ρ V = (α i).denote V)
    (V : History) (w : Valuation) (n : ℕ) :
    ((sharedBudgetedTrader Ts active α hα).strat n).value V w =
      ∑ i : Fin (n + 1), weight active (fun k => (α k).denote V) i *
        ((Ts i).strat n).value V w := by
  rw [sharedBudgetedTrader, Strategy.join_value]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Strategy.scaleBy_value, sharedFeatureWeight_denote active α hαc]

theorem sharedBudgetedTrader_magnitude (Ts : ℕ → Trader) (active : ℕ → ℕ → Bool)
    (α : ℕ → EF) (hα : ∀ i, (α i).rank ≤ i)
    (hαc : ∀ i ρ V, (α i).denoteWith ρ V = (α i).denote V)
    (V : History) (n : ℕ) :
    ((sharedBudgetedTrader Ts active α hα).strat n).magnitude V =
      ∑ i : Fin (n + 1), |weight active (fun k => (α k).denote V) i| *
        ((Ts i).strat n).magnitude V := by
  rw [sharedBudgetedTrader, Strategy.join_magnitude]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Strategy.scaleBy_magnitude, sharedFeatureWeight_denote active α hαc]

/-- Net worth of the shared sum is the finite weighted sum of component net worths.
The pre-launch-zero clause in `EfficientlyEmulatable` is what turns the triangular daily
bundle into this rectangular component view. -/
theorem sharedBudgetedTrader_netWorth (Ts : ℕ → Trader)
    (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hαrank : ∀ i, (α i).rank ≤ i)
    (hαc : ∀ i ρ V, (α i).denoteWith ρ V = (α i).denote V)
    (hTs : EfficientlyEmulatable Ts) (V : History) (v : PCWorld) :
    ∀ n,
      (sharedBudgetedTrader Ts active α hαrank).netWorth V v n =
        ∑ i : Fin (n + 1), weight active (fun k => (α k).denote V) i *
          (Ts i).netWorth V v n := by
  intro n
  induction n with
  | zero =>
      simpa [Trader.netWorth] using
        (sharedBudgetedTrader_value Ts active α hαrank hαc V v.payout 0)
  | succ n ih =>
      have hday := sharedBudgetedTrader_value Ts active α hαrank hαc V v.payout (n + 1)
      have hlaunch := hTs.netWorth_launch V v (n + 1)
      rw [Trader.netWorth_succ, hday, ih]
      conv_lhs =>
        rhs
        rw [Fin.sum_univ_castSucc]
      conv_rhs => rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [hlaunch]
      simp_rw [Trader.netWorth_succ, mul_add]
      rw [Finset.sum_add_distrib]
      ring


/-- The finite day-`n` sum of all component strategies launched by then, scaled by their
reified adaptive budget coefficients. -/
def budgetedTrader (Ts : ℕ → Trader) (active : ℕ → ℕ → Bool) (α : ℕ → EF)
    (hα : ∀ i, (α i).rank ≤ i) : Trader where
  strat n := Strategy.join (List.ofFn (fun i : Fin (n + 1) =>
    Strategy.scaleBy (featureWeight active α i)
      ((featureWeight_rank_le active α hα i).trans (by omega))
      ((Ts i).strat n)))

theorem budgetedTrader_value (Ts : ℕ → Trader) (active : ℕ → ℕ → Bool)
    (α : ℕ → EF) (hα : ∀ i, (α i).rank ≤ i) (V : History) (w : Valuation) (n : ℕ) :
    ((budgetedTrader Ts active α hα).strat n).value V w =
      ∑ i : Fin (n + 1), weight active (fun k => (α k).denote V) i *
        ((Ts i).strat n).value V w := by
  rw [budgetedTrader, Strategy.join_value]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Strategy.scaleBy_value, featureWeight_denote]

theorem budgetedTrader_magnitude (Ts : ℕ → Trader) (active : ℕ → ℕ → Bool)
    (α : ℕ → EF) (hα : ∀ i, (α i).rank ≤ i) (V : History) (n : ℕ) :
    ((budgetedTrader Ts active α hα).strat n).magnitude V =
      ∑ i : Fin (n + 1), |weight active (fun k => (α k).denote V) i| *
        ((Ts i).strat n).magnitude V := by
  rw [budgetedTrader, Strategy.join_magnitude]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Strategy.scaleBy_magnitude, featureWeight_denote]

theorem weight_eq (active : ℕ → ℕ → Bool) (α : ℕ → ℝ) (n : ℕ) :
    weight active α n = 1 - outstanding active α (weight active α) n := by
  rw [weight]
  rfl

/-- Once a component closes it stays closed.  Equivalently, openness at a later day
implies openness at every earlier day after the component was introduced. -/
def ClosingSchedule (active : ℕ → ℕ → Bool) : Prop :=
  ∀ i n, active i (n + 1) = true → active i n = true

/-- The central budgeting invariant.  If component magnitudes lie in `[0,1]` and open
positions only disappear, every adaptive coefficient is in `[0,1]`, and the capital
tied up after adding the current component is at most one unit. -/
theorem weight_nonneg_and_postAllocation_le
    (active : ℕ → ℕ → Bool) (α : ℕ → ℝ)
    (hclose : ClosingSchedule active)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1) :
    ∀ n, 0 ≤ weight active α n ∧
      outstanding active α (weight active α) n + weight active α n * α n ≤ 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hw0 : ∀ i < n, 0 ≤ weight active α i := fun i hi => (ih i hi).1
      have hterm0 : ∀ i : Fin n,
          0 ≤ (if active i n then weight active α i * α i else 0) := by
        intro i
        split <;> simp_all only [le_refl]
        exact mul_nonneg (hw0 i i.isLt) (hα0 i)
      have hout0 : 0 ≤ outstanding active α (weight active α) n := by
        exact Finset.sum_nonneg (fun i hi => hterm0 i)
      have hout1 : outstanding active α (weight active α) n ≤ 1 := by
        cases n with
        | zero => simp [outstanding]
        | succ k =>
            have hprev := (ih k (by omega)).2
            rw [outstanding, Fin.sum_univ_castSucc]
            have hsum :
                (∑ i : Fin k, if active (Fin.castSucc i) (k + 1) then
                    weight active α (Fin.castSucc i) * α (Fin.castSucc i) else 0) ≤
                  outstanding active α (weight active α) k := by
              rw [outstanding]
              apply Finset.sum_le_sum
              intro i hi
              by_cases hop : active i (k + 1) = true
              · have hop' : active i k = true := hclose i k hop
                simp [hop, hop']
              · simp [hop]
                by_cases hop' : active i k = true
                · simp [hop', mul_nonneg (hw0 i (by omega)) (hα0 i)]
                · simp [hop']
            have hlast :
                (if active (Fin.last k) (k + 1) then
                    weight active α (Fin.last k) * α (Fin.last k) else 0) ≤
                  weight active α k * α k := by
              simp only [Fin.val_last]
              split
              · exact le_rfl
              · exact mul_nonneg (hw0 k (by omega)) (hα0 k)
            exact le_trans (add_le_add hsum hlast) hprev
      have hw : weight active α n = 1 - outstanding active α (weight active α) n :=
        weight_eq active α n
      constructor
      · rw [hw]
        linarith
      · rw [hw]
        nlinarith [hα0 n, hα1 n]

theorem weight_nonneg
    (active : ℕ → ℕ → Bool) (α : ℕ → ℝ)
    (hclose : ClosingSchedule active)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1) (n : ℕ) :
    0 ≤ weight active α n :=
  (weight_nonneg_and_postAllocation_le active α hclose hα0 hα1 n).1

theorem weight_le_one
    (active : ℕ → ℕ → Bool) (α : ℕ → ℝ)
    (hclose : ClosingSchedule active)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1) (n : ℕ) :
    weight active α n ≤ 1 := by
  rw [weight_eq]
  exact sub_le_self _ (Finset.sum_nonneg (fun i hi => by
    split
    · exact mul_nonneg (weight_nonneg active α hclose hα0 hα1 i) (hα0 i)
    · exact le_rfl))

/-- Capital allocated to component `i`. -/
noncomputable def allocation (active : ℕ → ℕ → Bool) (α : ℕ → ℝ) (i : ℕ) : ℝ :=
  weight active α i * α i

/-- Total allocation launched through component `n`. -/
noncomputable def allocationPrefix (active : ℕ → ℕ → Bool) (α : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin (n + 1), allocation active α i

/-- Allocation still open on day `n`, including the newly launched component when active. -/
noncomputable def activeAllocation (active : ℕ → ℕ → Bool) (α : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin (n + 1), if active i n then allocation active α i else 0

theorem allocation_nonneg (active : ℕ → ℕ → Bool) (α : ℕ → ℝ)
    (hclose : ClosingSchedule active) (hα0 : ∀ i, 0 ≤ α i)
    (hα1 : ∀ i, α i ≤ 1) (i : ℕ) :
    0 ≤ allocation active α i :=
  mul_nonneg (weight_nonneg active α hclose hα0 hα1 i) (hα0 i)

/-- At most one unit of allocation is active at a time. -/
theorem activeAllocation_le_one (active : ℕ → ℕ → Bool) (α : ℕ → ℝ)
    (hclose : ClosingSchedule active) (hα0 : ∀ i, 0 ≤ α i)
    (hα1 : ∀ i, α i ≤ 1) (n : ℕ) :
    activeAllocation active α n ≤ 1 := by
  rw [activeAllocation, Fin.sum_univ_castSucc]
  have hbudget := (weight_nonneg_and_postAllocation_le active α hclose hα0 hα1 n).2
  have hprior :
      (∑ i : Fin n, if active (Fin.castSucc i) n then
          allocation active α (Fin.castSucc i) else 0) =
        outstanding active α (weight active α) n := by
    rw [outstanding]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Fin.coe_castSucc, allocation]
  rw [hprior]
  simp only [Fin.val_last]
  by_cases h : active n n = true
  · simp [h, allocation] at hbudget ⊢
    exact hbudget
  · simp [h]
    exact le_trans (le_add_of_nonneg_right
      (allocation_nonneg active α hclose hα0 hα1 n)) hbudget

/-- Finite tails of a nonnegative summable real series are uniformly small. -/
theorem summable_tail_Ico_lt {f : ℕ → ℝ} (hf0 : ∀ i, 0 ≤ f i)
    (hf : Summable f) {r : ℝ} (hr : 0 < r) :
    ∃ K, ∀ n, K ≤ n → ∑ i ∈ Finset.Ico K n, f i < r := by
  have htend := hf.hasSum.tendsto_sum_nat
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp htend r hr
  refine ⟨K, fun n hKn => ?_⟩
  have hnear := hK K le_rfl
  rw [Real.dist_eq, abs_lt] at hnear
  have hnle : (∑ i ∈ Finset.range n, f i) ≤ ∑' i, f i :=
    hf.sum_le_tsum _ (fun i _ => hf0 i)
  have hsplit := Finset.sum_range_add_sum_Ico f hKn
  linarith

/-- If every component eventually closes and component magnitudes are frequently bounded
away from zero, the unit budget is recycled infinitely often: cumulative allocation is not
bounded above. This is the sparse-opportunity form needed by the paper's repeatable-ROI
lemma; components with zero magnitude on non-opportunity days are harmless. -/
theorem allocationPrefix_not_bddAbove_of_frequently
    (close : ℕ → ℕ) (active : ℕ → ℕ → Bool)
    (hclosing : ClosingSchedule active)
    (hclosed : ∀ i n, close i ≤ n → active i n = false) (α : ℕ → ℝ)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hδα : ∃ᶠ i in Filter.atTop, δ ≤ α i) :
    ¬ BddAbove (Set.range (allocationPrefix active α)) := by
  have ha0 : ∀ i, 0 ≤ allocation active α i :=
    fun i => allocation_nonneg active α hclosing hα0 hα1 i
  intro hbdd
  obtain ⟨B, hB⟩ := hbdd
  have hsumRange : ∀ n, (∑ i ∈ Finset.range n, allocation active α i) ≤ B := by
    intro n
    cases n with
    | zero =>
        have hbase := hB (show allocationPrefix active α 0 ∈
          Set.range (allocationPrefix active α) from ⟨0, rfl⟩)
        have hbase0 : 0 ≤ allocationPrefix active α 0 :=
          Finset.sum_nonneg (fun i _ => ha0 i)
        simp only [Finset.sum_range_zero]
        linarith
    | succ n =>
        have hn := hB (show allocationPrefix active α n ∈
          Set.range (allocationPrefix active α) from ⟨n, rfl⟩)
        rw [allocationPrefix, Fin.sum_univ_eq_sum_range] at hn
        exact hn
  have haSum : Summable (allocation active α) :=
    summable_of_sum_range_le ha0 hsumRange
  let r : ℝ := min (1 / 2 : ℝ) (δ / 2)
  have hr : 0 < r := lt_min (by norm_num) (half_pos hδ)
  obtain ⟨K, htail⟩ := summable_tail_Ico_lt ha0 haSum hr
  let N := K + ∑ i ∈ Finset.range K, close i
  have hKN : K ≤ N := by simp [N]
  obtain ⟨J, hNJ, hαJ⟩ := (Filter.frequently_atTop.mp hδα) N
  have hKJ : K ≤ J := hKN.trans hNJ
  have hcloseBefore : ∀ i < K, close i ≤ N := by
    intro i hi
    have himem : i ∈ Finset.range K := Finset.mem_range.mpr hi
    have hile : close i ≤ ∑ j ∈ Finset.range K, close j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (close j)) himem
    dsimp [N]
    omega
  have hout : outstanding active α (weight active α) J < r := by
    have houtLe : outstanding active α (weight active α) J ≤
        ∑ i ∈ Finset.Ico K J, allocation active α i := by
      rw [outstanding]
      calc
        (∑ i : Fin J,
            if active i J then weight active α i * α i else 0) ≤
            ∑ i : Fin J,
              if K ≤ i then allocation active α i else 0 := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hop : active i J = true
          · have hKi : K ≤ i := by
              by_contra hnot
              have hiK : i < K := Nat.lt_of_not_ge hnot
              have hci := hcloseBefore i hiK
              have hf := hclosed i J (hci.trans hNJ)
              rw [hf] at hop
              contradiction
            simp [hop, hKi, allocation]
          · have hfalse := Bool.eq_false_of_not_eq_true hop
            simp [hfalse]
            split
            · exact ha0 i
            · exact le_rfl
        _ = ∑ i ∈ Finset.Ico K J, allocation active α i := by
          rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
            if K ≤ i then allocation active α i else 0)]
          rw [← Finset.sum_filter]
          congr 1
          ext i
          simp [Finset.mem_Ico]
          omega
    exact lt_of_le_of_lt houtLe (htail J hKJ)
  have hβhalf : (1 / 2 : ℝ) < weight active α J := by
    rw [weight_eq]
    have hrhalf : r ≤ (1 / 2 : ℝ) := min_le_left _ _
    linarith
  have haJlower : δ / 2 < allocation active α J := by
    dsimp [allocation]
    calc
      δ / 2 = (1 / 2 : ℝ) * δ := by ring
      _ < weight active α J * δ :=
        mul_lt_mul_of_pos_right hβhalf hδ
      _ ≤ weight active α J * α J :=
        mul_le_mul_of_nonneg_left hαJ
          (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) (le_of_lt hβhalf))
  have htailNext := htail (J + 1) (by omega)
  have haJtail : allocation active α J ≤
      ∑ i ∈ Finset.Ico K (J + 1), allocation active α i := by
    apply Finset.single_le_sum (fun i _ => ha0 i)
    simp [Finset.mem_Ico, hKJ]
  have hrδ : r ≤ δ / 2 := min_le_right _ _
  linarith

/-- Uniformly positive magnitudes are the immediate special case of sparse recycling. -/
theorem allocationPrefix_not_bddAbove (close : ℕ → ℕ) (active : ℕ → ℕ → Bool)
    (hclosing : ClosingSchedule active)
    (hclosed : ∀ i n, close i ≤ n → active i n = false) (α : ℕ → ℝ)
    (hα0 : ∀ i, 0 ≤ α i) (hα1 : ∀ i, α i ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hδα : ∀ i, δ ≤ α i) :
    ¬ BddAbove (Set.range (allocationPrefix active α)) := by
  apply allocationPrefix_not_bddAbove_of_frequently close active hclosing hclosed α
    hα0 hα1 hδ
  exact Filter.frequently_atTop.mpr (fun N => ⟨N, le_rfl, hδα N⟩)

/-! ### From ROI maturity to a closing schedule -/

/-- Keep component `i` active strictly before its selected closing day. -/
def activeUntil (close : ℕ → ℕ) (i n : ℕ) : Bool := decide (n < close i)

theorem activeUntil_closing (close : ℕ → ℕ) : ClosingSchedule (activeUntil close) := by
  intro i n h
  simp [activeUntil] at h ⊢
  omega

theorem activeUntil_eventually_closed (close : ℕ → ℕ) (i : ℕ) :
    ∃ N, ∀ n, N ≤ n → activeUntil close i n = false := by
  refine ⟨close i, fun n hn => ?_⟩
  simp [activeUntil]
  omega

/-- After a maturity day, at most an `η` fraction of the component's total magnitude
remains to be traded. -/
theorem tail_magnitude_le_of_matured (Tr : Trader) (V : History)
    (DP : DeductiveProcess) (ε η : ℝ) (m n : ℕ)
    (hroi : HasROI Tr V DP ε) (hm : Tr.Matured V DP ε η m) (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico (m + 1) (n + 1), (Tr.strat i).magnitude V) ≤
      η * Tr.magnitude V := by
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun i => (Tr.strat i).magnitude V) (show m + 1 ≤ n + 1 by omega)
  have hpartial := Tr.partial_magnitude_le V hroi.1 n
  have hmagnitude := hm.1
  linarith

/-- A matured positive-ROI component remains profitable at every later plausible day,
up to one additional `η` fraction for its post-maturity trading tail. -/
theorem netWorth_lower_of_matured (Tr : Trader) (V : History)
    (DP : DeductiveProcess) (ε η : ℝ) (m n : ℕ)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hroi : HasROI Tr V DP ε) (hm : Tr.Matured V DP ε η m)
    (hmn : m ≤ n) (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    (ε - 2 * η) * Tr.magnitude V ≤ Tr.netWorth V v n := by
  have hsub : DP.D m ⊆ DP.D n := Finset.le_iff_subset.mp
    (monotone_nat_of_le_succ (fun k => Finset.le_iff_subset.mpr (DP.mono k)) hmn)
  have hvm : v.ConsistentWith (DP.D m) := fun φ hφ => hv φ (hsub hφ)
  have hprofit := hm.2 v hvm
  have htailMag := tail_magnitude_le_of_matured Tr V DP ε η m n hroi hm hmn
  have htailValue :
      -(∑ i ∈ Finset.Ico (m + 1) (n + 1), (Tr.strat i).magnitude V) ≤
        ∑ i ∈ Finset.Ico (m + 1) (n + 1),
          (Tr.strat i).value V v.payout := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun i hi =>
      neg_le_of_abs_le (Strategy.abs_value_le_magnitude
        (Tr.strat i) V v.payout (fun φ => by
          by_cases hφ : v.Holds φ
          · exact Or.inr (by simp [PCWorld.payout, hφ])
          · exact Or.inl (by simp [PCWorld.payout, hφ])) (hP i)))
  have hsplitWorth := Finset.sum_range_add_sum_Ico
    (fun i => (Tr.strat i).value V v.payout) (show m + 1 ≤ n + 1 by omega)
  rw [← Trader.netWorth] at hsplitWorth
  rw [← Trader.netWorth] at hsplitWorth
  nlinarith [Trader.magnitude_nonneg Tr V]

/-- A selected closing day and tolerance for every component. -/
def MaturitySchedule (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    (ε : ℝ) (η : ℕ → ℝ) (close : ℕ → ℕ) : Prop :=
  ∀ i, (Ts i).Matured V DP ε (η i) (close i)

/-! ## Polynomial bounded-verification bridge

The paper does not require the first maturity day itself to be polynomially computable.
It requires each finite maturity claim to be checkable efficiently.  On budget day `k` we
therefore scan only the prefix `m ≤ k`; `polyFueled_boundedNone` turns that bounded scan into
the openness table consumed by the shared trader.
-/

/-- A uniformly polynomial, sound, eventually successful verifier for component maturity.
The checker input is `⟨component, day⟩`. -/
structure VerifiedMaturitySchedule (Ts : ℕ → Trader) (V : History)
    (DP : DeductiveProcess) (ε : ℝ) (η : ℕ → ℝ) where
  check : ℕ → ℕ → Bool
  check_poly : ∃ c, PolyFueled c
    (fun z => if check z.unpair.1 z.unpair.2 then 1 else 0)
  sound : ∀ i m, check i m = true → (Ts i).Matured V DP ε (η i) m
  complete : ∀ i, ∃ m, check i m = true

/-- The first verified maturity day.  This value may be selected noncomputably; queries of
the form “is it after day `k`?” are nevertheless polynomial by bounded verification. -/
noncomputable def VerifiedMaturitySchedule.close
    {Ts : ℕ → Trader} {V : History} {DP : DeductiveProcess} {ε : ℝ} {η : ℕ → ℝ}
    (h : VerifiedMaturitySchedule Ts V DP ε η) (i : ℕ) : ℕ :=
  Nat.find (h.complete i)

theorem VerifiedMaturitySchedule.check_close
    {Ts : ℕ → Trader} {V : History} {DP : DeductiveProcess} {ε : ℝ} {η : ℕ → ℝ}
    (h : VerifiedMaturitySchedule Ts V DP ε η) (i : ℕ) :
    h.check i (h.close i) = true :=
  Nat.find_spec (h.complete i)

theorem VerifiedMaturitySchedule.check_false_of_lt_close
    {Ts : ℕ → Trader} {V : History} {DP : DeductiveProcess} {ε : ℝ} {η : ℕ → ℝ}
    (h : VerifiedMaturitySchedule Ts V DP ε η) {i m : ℕ} (hm : m < h.close i) :
    h.check i m = false := by
  apply Bool.eq_false_of_not_eq_true
  exact Nat.find_min (h.complete i) hm

theorem VerifiedMaturitySchedule.boundedNone_eq_activeUntil
    {Ts : ℕ → Trader} {V : History} {DP : DeductiveProcess} {ε : ℝ} {η : ℕ → ℝ}
    (h : VerifiedMaturitySchedule Ts V DP ε η) (i k : ℕ) :
    boundedNone h.check i k = activeUntil h.close i k := by
  apply Bool.eq_iff_iff.mpr
  rw [boundedNone_eq_true_iff]
  simp only [activeUntil, decide_eq_true_eq]
  constructor
  · intro hall
    by_contra hnot
    have hle : h.close i ≤ k := by omega
    have := hall (h.close i) hle
    rw [h.check_close i] at this
    contradiction
  · intro hlt m hm
    exact h.check_false_of_lt_close (lt_of_le_of_lt hm hlt)

theorem VerifiedMaturitySchedule.polyActive
    {Ts : ℕ → Trader} {V : History} {DP : DeductiveProcess} {ε : ℝ} {η : ℕ → ℝ}
    (h : VerifiedMaturitySchedule Ts V DP ε η) :
    PolyActiveSchedule (activeUntil h.close) := by
  obtain ⟨c, hc⟩ := polyFueled_boundedNone h.check h.check_poly
  have hswap := hc.comp (PolyFueled.right.pair PolyFueled.left)
  refine ⟨_, hswap.of_eq (fun z => ?_)⟩
  simp only [Function.comp_apply, Nat.unpair_pair]
  rw [h.boundedNone_eq_activeUntil]

theorem VerifiedMaturitySchedule.maturity
    {Ts : ℕ → Trader} {V : History} {DP : DeductiveProcess} {ε : ℝ} {η : ℕ → ℝ}
    (h : VerifiedMaturitySchedule Ts V DP ε η) :
    MaturitySchedule Ts V DP ε η h.close :=
  fun i => h.sound i (h.close i) (h.check_close i)

/-- Quantitative lower bound for the repeatable-ROI bundle. Total launched allocation earns
`ε`; at most one unit remains active, and the summable maturity tolerances pay for every
closed component's post-maturity tail. -/
theorem sharedBudgetedTrader_netWorth_lower
    (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ) (close : ℕ → ℕ)
    (α : ℕ → EF) (hαrank : ∀ i, (α i).rank ≤ i)
    (hαc : ∀ i ρ W, (α i).denoteWith ρ W = (α i).denote W)
    (hmag : ∀ i, (α i).denote V = (Ts i).magnitude V)
    (hα0 : ∀ i, 0 ≤ (α i).denote V) (hα1 : ∀ i, (α i).denote V ≤ 1)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hemul : EfficientlyEmulatable Ts)
    (hroi : ∀ i, HasROI (Ts i) V DP ε)
    (hη0 : ∀ i, 0 ≤ η i) (hηsum : Summable η)
    (hmature : MaturitySchedule Ts V DP ε η close)
    (n : ℕ) (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    ε * allocationPrefix (activeUntil close) (fun i => (α i).denote V) n -
        (ε + 1) - 2 * ∑' i, η i ≤
      (sharedBudgetedTrader Ts (activeUntil close) α hαrank).netWorth V v n := by
  let M : ℕ → ℝ := fun i => (α i).denote V
  let active := activeUntil close
  have hclosing : ClosingSchedule active := activeUntil_closing close
  have hβ0 : ∀ i, 0 ≤ weight active M i :=
    fun i => weight_nonneg active M hclosing hα0 hα1 i
  have halloc0 : ∀ i, 0 ≤ allocation active M i :=
    fun i => allocation_nonneg active M hclosing hα0 hα1 i
  have halloc1 : ∀ i, allocation active M i ≤ 1 := by
    intro i
    dsimp [allocation]
    calc
      weight active M i * M i ≤ 1 * M i :=
        mul_le_mul_of_nonneg_right
          (weight_le_one active M hclosing hα0 hα1 i) (hα0 i)
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left (hα1 i) zero_le_one
      _ = 1 := one_mul 1
  have hactive : activeAllocation active M n ≤ 1 :=
    activeAllocation_le_one active M hclosing hα0 hα1 n
  have htol : (∑ i : Fin (n + 1), η i * allocation active M i) ≤ ∑' i, η i := by
    calc
      (∑ i : Fin (n + 1), η i * allocation active M i) ≤
          ∑ i : Fin (n + 1), η i := Finset.sum_le_sum (fun i _ => by
            exact mul_le_of_le_one_right (hη0 i) (halloc1 i))
      _ = ∑ i ∈ Finset.range (n + 1), η i := by
        rw [Fin.sum_univ_eq_sum_range]
      _ ≤ ∑' i, η i := hηsum.sum_le_tsum _ (fun i _ => hη0 i)
  have hpoint : ∀ i : Fin (n + 1),
      ε * allocation active M i -
          (ε + 1) * (if active i n then allocation active M i else 0) -
          2 * (η i * allocation active M i) ≤
        weight active M i * (Ts i).netWorth V v n := by
    intro i
    by_cases hop : active i n = true
    · have hnw : -M i ≤ (Ts i).netWorth V v n := by
        change -(α i).denote V ≤ (Ts i).netWorth V v n
        rw [hmag i]
        exact neg_le_of_abs_le
          ((Ts i).abs_netWorth_le_magnitude V v hP (hroi i).1 n)
      have hscaled := mul_le_mul_of_nonneg_left hnw (hβ0 i)
      simp only [hop, if_true]
      have htol0 := mul_nonneg (hη0 i) (halloc0 i)
      calc
        ε * allocation active M i - (ε + 1) * allocation active M i -
              2 * (η i * allocation active M i) ≤ -allocation active M i := by
            nlinarith
        _ = weight active M i * -M i := by simp [allocation]
        _ ≤ weight active M i * (Ts i).netWorth V v n := hscaled
    · have hclosed : close i ≤ n := by
        change ¬activeUntil close i n = true at hop
        simp [activeUntil] at hop
        omega
      have hnw := netWorth_lower_of_matured (Ts i) V DP ε (η i) (close i) n
        hP (hroi i) (hmature i) hclosed v hv
      rw [← hmag i] at hnw
      have hscaled := mul_le_mul_of_nonneg_left hnw (hβ0 i)
      have hfalse : active i n = false := Bool.eq_false_of_not_eq_true hop
      simp only [hfalse, if_false]
      calc
        ε * allocation active M i - (ε + 1) * 0 -
              2 * (η i * allocation active M i) =
            weight active M i * ((ε - 2 * η i) * M i) := by
              simp [allocation]
              ring
        _ ≤ weight active M i * (Ts i).netWorth V v n := hscaled
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hcoarse :
      (∑ i : Fin (n + 1),
        (ε * allocation active M i -
          (ε + 1) * (if active i n then allocation active M i else 0) -
          2 * (η i * allocation active M i))) =
        ε * allocationPrefix active M n -
          (ε + 1) * activeAllocation active M n -
          2 * (∑ i : Fin (n + 1), η i * allocation active M i) := by
    simp only [Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rfl
  rw [hcoarse] at hsum
  have hnet := sharedBudgetedTrader_netWorth Ts active α hαrank hαc hemul
  rw [hnet V v n]
  dsimp [active, M] at hsum ⊢
  nlinarith

/-- Semantic repeatable-ROI capstone once the allocation process is known to be unbounded.
The same quantitative estimate supplies both halves of exploitation: bounded downside from
the unit active budget and summable tails, and unbounded upside from recycled allocation. -/
theorem sharedBudgetedTrader_exploits_of_unboundedAllocation
    (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ) (close : ℕ → ℕ)
    (α : ℕ → EF) (hαrank : ∀ i, (α i).rank ≤ i)
    (hαc : ∀ i ρ W, (α i).denoteWith ρ W = (α i).denote W)
    (hmag : ∀ i, (α i).denote V = (Ts i).magnitude V)
    (hα0 : ∀ i, 0 ≤ (α i).denote V) (hα1 : ∀ i, (α i).denote V ≤ 1)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hemul : EfficientlyEmulatable Ts)
    (hroi : ∀ i, HasROI (Ts i) V DP ε)
    (hη0 : ∀ i, 0 ≤ η i) (hηsum : Summable η)
    (hmature : MaturitySchedule Ts V DP ε η close)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hunbounded : ¬ BddAbove (Set.range
      (allocationPrefix (activeUntil close) (fun i => (α i).denote V)))) :
    (sharedBudgetedTrader Ts (activeUntil close) α hαrank).Exploits V DP := by
  let Tr := sharedBudgetedTrader Ts (activeUntil close) α hαrank
  have hlower := sharedBudgetedTrader_netWorth_lower Ts V DP ε hε η close α
    hαrank hαc hmag hα0 hα1 hP hemul hroi hη0 hηsum hmature
  constructor
  · refine ⟨-(ε + 1) - 2 * ∑' i, η i, ?_⟩
    rintro x ⟨n, v, hv, rfl⟩
    have h := hlower n v hv
    have ha0 : 0 ≤ allocationPrefix (activeUntil close)
        (fun i => (α i).denote V) n := by
      exact Finset.sum_nonneg (fun i _ => allocation_nonneg
        (activeUntil close) (fun i => (α i).denote V)
        (activeUntil_closing close) hα0 hα1 i)
    nlinarith
  · intro hbdd
    obtain ⟨B, hB⟩ := hbdd
    obtain ⟨A, ⟨n, rfl⟩, hA⟩ := not_bddAbove_iff.mp hunbounded
      ((B + (ε + 1) + 2 * ∑' i, η i) / ε)
    obtain ⟨v, hv⟩ := hworld n
    have hlo := hlower n v hv
    have hmem : Tr.netWorth V v n ∈ Tr.plausibleAssessments V DP :=
      ⟨n, v, hv, rfl⟩
    have hup := hB hmem
    dsimp [Tr] at hlo hmem hup
    have hεne : ε ≠ 0 := ne_of_gt hε
    field_simp [hεne] at hA
    nlinarith

/-- Repeatable positive ROI is exploitable: eventual closure recycles the unit budget, and
a uniform positive magnitude floor makes cumulative allocation unbounded. -/
theorem sharedBudgetedTrader_exploits
    (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ) (close : ℕ → ℕ)
    (α : ℕ → EF) (hαrank : ∀ i, (α i).rank ≤ i)
    (hαc : ∀ i ρ W, (α i).denoteWith ρ W = (α i).denote W)
    (hmag : ∀ i, (α i).denote V = (Ts i).magnitude V)
    (hα0 : ∀ i, 0 ≤ (α i).denote V) (hα1 : ∀ i, (α i).denote V ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hδα : ∀ i, δ ≤ (α i).denote V)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hemul : EfficientlyEmulatable Ts)
    (hroi : ∀ i, HasROI (Ts i) V DP ε)
    (hη0 : ∀ i, 0 ≤ η i) (hηsum : Summable η)
    (hmature : MaturitySchedule Ts V DP ε η close)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (sharedBudgetedTrader Ts (activeUntil close) α hαrank).Exploits V DP := by
  apply sharedBudgetedTrader_exploits_of_unboundedAllocation Ts V DP ε hε η close α
    hαrank hαc hmag hα0 hα1 hP hemul hroi hη0 hηsum hmature hworld
  exact allocationPrefix_not_bddAbove close (activeUntil close)
    (activeUntil_closing close) (fun i n hn => by
      simp [activeUntil]
      omega) (fun i => (α i).denote V) hα0 hα1 hδ hδα

/-- Sparse repeatable positive ROI is exploitable: it is enough that component magnitudes
are bounded away from zero infinitely often. Zero-magnitude components between profitable
opportunities consume no allocation and do not obstruct recycling. -/
theorem sharedBudgetedTrader_exploits_of_frequently
    (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ) (close : ℕ → ℕ)
    (α : ℕ → EF) (hαrank : ∀ i, (α i).rank ≤ i)
    (hαc : ∀ i ρ W, (α i).denoteWith ρ W = (α i).denote W)
    (hmag : ∀ i, (α i).denote V = (Ts i).magnitude V)
    (hα0 : ∀ i, 0 ≤ (α i).denote V) (hα1 : ∀ i, (α i).denote V ≤ 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hδα : ∃ᶠ i in Filter.atTop, δ ≤ (α i).denote V)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hemul : EfficientlyEmulatable Ts)
    (hroi : ∀ i, HasROI (Ts i) V DP ε)
    (hη0 : ∀ i, 0 ≤ η i) (hηsum : Summable η)
    (hmature : MaturitySchedule Ts V DP ε η close)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (sharedBudgetedTrader Ts (activeUntil close) α hαrank).Exploits V DP := by
  apply sharedBudgetedTrader_exploits_of_unboundedAllocation Ts V DP ε hε η close α
    hαrank hαc hmag hα0 hα1 hP hemul hroi hη0 hηsum hmature hworld
  exact allocationPrefix_not_bddAbove_of_frequently close (activeUntil close)
    (activeUntil_closing close) (fun i n hn => by
      simp [activeUntil]
      omega) (fun i => (α i).denote V) hα0 hα1 hδ hδα

/-- Full repeatable-ROI hub: the shared budget trader is both faithfully polynomial-time
token-computable and exploiting. -/
theorem repeatableROI
    (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ) (close : ℕ → ℕ)
    (α : ℕ → EF) (hαrank : ∀ i, (α i).rank ≤ i)
    (hαseg : PolySegStream (fun i => (α i).serialize))
    (hαc : ∀ i ρ W, (α i).denoteWith ρ W = (α i).denote W)
    (hmag : ∀ i, (α i).denote V = (Ts i).magnitude V)
    (hα0 : ∀ i, 0 ≤ (α i).denote V) (hα1 : ∀ i, (α i).denote V ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hδα : ∀ i, δ ≤ (α i).denote V)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hTs : PolyTradeEmulatable Ts)
    (hactive : PolyActiveSchedule (activeUntil close))
    (hroi : ∀ i, HasROI (Ts i) V DP ε)
    (hη0 : ∀ i, 0 ≤ η i) (hηsum : Summable η)
    (hmature : MaturitySchedule Ts V DP ε η close)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    EfficientlyComputableTok
        (sharedBudgetedTrader Ts (activeUntil close) α hαrank) ∧
      (sharedBudgetedTrader Ts (activeUntil close) α hαrank).Exploits V DP := by
  constructor
  · exact sharedBudgetedTrader_ecTok Ts (activeUntil close) α hαrank hαseg hactive hTs
  · exact sharedBudgetedTrader_exploits Ts V DP ε hε η close α hαrank hαc hmag
      hα0 hα1 hδ hδα hP hTs.emulatable hroi hη0 hηsum hmature hworld

/-- Sparse form of the full repeatable-ROI construction. -/
theorem repeatableROI_of_frequently
    (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ) (close : ℕ → ℕ)
    (α : ℕ → EF) (hαrank : ∀ i, (α i).rank ≤ i)
    (hαseg : PolySegStream (fun i => (α i).serialize))
    (hαc : ∀ i ρ W, (α i).denoteWith ρ W = (α i).denote W)
    (hmag : ∀ i, (α i).denote V = (Ts i).magnitude V)
    (hα0 : ∀ i, 0 ≤ (α i).denote V) (hα1 : ∀ i, (α i).denote V ≤ 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hδα : ∃ᶠ i in Filter.atTop, δ ≤ (α i).denote V)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hTs : PolyTradeEmulatable Ts)
    (hactive : PolyActiveSchedule (activeUntil close))
    (hroi : ∀ i, HasROI (Ts i) V DP ε)
    (hη0 : ∀ i, 0 ≤ η i) (hηsum : Summable η)
    (hmature : MaturitySchedule Ts V DP ε η close)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    EfficientlyComputableTok
        (sharedBudgetedTrader Ts (activeUntil close) α hαrank) ∧
      (sharedBudgetedTrader Ts (activeUntil close) α hαrank).Exploits V DP := by
  constructor
  · exact sharedBudgetedTrader_ecTok Ts (activeUntil close) α hαrank hαseg hactive hTs
  · exact sharedBudgetedTrader_exploits_of_frequently Ts V DP ε hε η close α hαrank
      hαc hmag hα0 hα1 hδ hδα hP hTs.emulatable hroi hη0 hηsum hmature hworld

/-- `lem:type3`, operational paper-facing form: a logical inductor admits no efficiently
repeatable family with fixed positive ROI and a polynomial maturity verifier unless the
component magnitudes converge to zero. -/
theorem noRepeatableROI
    (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor V DP]
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ) (close : ℕ → ℕ)
    (α : ℕ → EF) (hαrank : ∀ i, (α i).rank ≤ i)
    (hαseg : PolySegStream (fun i => (α i).serialize))
    (hαc : ∀ i ρ W, (α i).denoteWith ρ W = (α i).denote W)
    (hmag : ∀ i, (α i).denote V = (Ts i).magnitude V)
    (hα0 : ∀ i, 0 ≤ (α i).denote V) (hα1 : ∀ i, (α i).denote V ≤ 1)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hTs : PolyTradeEmulatable Ts)
    (hactive : PolyActiveSchedule (activeUntil close))
    (hroi : ∀ i, HasROI (Ts i) V DP ε)
    (hη0 : ∀ i, 0 ≤ η i) (hηsum : Summable η)
    (hmature : MaturitySchedule Ts V DP ε η close)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun i => (α i).denote V) 0 := by
  refine Metric.tendsto_atTop.mpr (fun δ hδ => ?_)
  have hnotfreq : ¬ ∃ᶠ i in Filter.atTop, δ ≤ (α i).denote V := by
    intro hfreq
    obtain ⟨hec, hex⟩ := repeatableROI_of_frequently Ts V DP ε hε η close α hαrank
      hαseg hαc hmag hα0 hα1 hδ hfreq hP hTs hactive hroi hη0 hηsum hmature hworld
    exact hLI.noExploit _ hec hex
  rw [Filter.not_frequently] at hnotfreq
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hnotfreq
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hα0 n)]
  exact lt_of_not_ge (hN n hn)

/-- Paper-facing verifier form of `noRepeatableROI`.  Callers provide only a polynomial,
sound, eventually successful maturity checker; the bounded-verification bridge constructs
the closing days, semantic maturity schedule, and polynomial openness table. -/
theorem noRepeatableROI_of_verifiedMaturity
    (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor V DP]
    (ε : ℝ) (hε : 0 < ε) (η : ℕ → ℝ)
    (α : ℕ → EF) (hαrank : ∀ i, (α i).rank ≤ i)
    (hαseg : PolySegStream (fun i => (α i).serialize))
    (hαc : ∀ i ρ W, (α i).denoteWith ρ W = (α i).denote W)
    (hmag : ∀ i, (α i).denote V = (Ts i).magnitude V)
    (hα0 : ∀ i, 0 ≤ (α i).denote V) (hα1 : ∀ i, (α i).denote V ≤ 1)
    (hP : ∀ d φ, 0 ≤ V d φ ∧ V d φ ≤ 1)
    (hTs : PolyTradeEmulatable Ts)
    (hroi : ∀ i, HasROI (Ts i) V DP ε)
    (hη0 : ∀ i, 0 ≤ η i) (hηsum : Summable η)
    (hver : VerifiedMaturitySchedule Ts V DP ε η)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun i => (α i).denote V) 0 := by
  exact noRepeatableROI Ts V DP ε hε η hver.close α hαrank hαseg hαc hmag hα0 hα1
    hP hTs hver.polyActive hroi hη0 hηsum hver.maturity hworld

/-- A semantic closing day selected from each member's ROI witness. This is deliberately
noncomputable: the paper-facing construction instead uses a bounded verification search
built from the computable market/process certificates carried by `IsLogicalInductor`. -/
noncomputable def maturityDay (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    (ε η : ℝ) (hroi : ∀ i, HasROI (Ts i) V DP ε) (hη : 0 < η) (i : ℕ) : ℕ :=
  Classical.choose ((hroi i).exists_matured hη)

theorem maturityDay_spec (Ts : ℕ → Trader) (V : History) (DP : DeductiveProcess)
    (ε η : ℝ) (hroi : ∀ i, HasROI (Ts i) V DP ε) (hη : 0 < η) (i : ℕ) :
    (Ts i).Matured V DP ε η (maturityDay Ts V DP ε η hroi hη i) :=
  Classical.choose_spec ((hroi i).exists_matured hη)

theorem maturitySchedule_closing (Ts : ℕ → Trader) (V : History)
    (DP : DeductiveProcess) (ε η : ℝ) (hroi : ∀ i, HasROI (Ts i) V DP ε)
    (hη : 0 < η) :
    ClosingSchedule (activeUntil (maturityDay Ts V DP ε η hroi hη)) :=
  activeUntil_closing _

#print axioms weight_nonneg_and_postAllocation_le
#print axioms maturityDay_spec
#print axioms featureWeight_denote
#print axioms budgetedTrader_value
#print axioms budgetedTrader_magnitude
#print axioms sharedFeatureWeight_denote
#print axioms sharedFeatureWeight_rank_le
#print axioms sharedFeatureWeight_cost_eq
#print axioms sharedFeatureWeight_polySeg
#print axioms sharedBudgetedTrader_value
#print axioms sharedBudgetedTrader_magnitude
#print axioms sharedBudgetedTrader_ecTok
#print axioms sharedBudgetedTrader_netWorth_lower
#print axioms allocationPrefix_not_bddAbove
#print axioms allocationPrefix_not_bddAbove_of_frequently
#print axioms sharedBudgetedTrader_exploits
#print axioms repeatableROI
#print axioms noRepeatableROI
#print axioms VerifiedMaturitySchedule.polyActive
#print axioms noRepeatableROI_of_verifiedMaturity

end ROIBudget

end LogicalInduction
