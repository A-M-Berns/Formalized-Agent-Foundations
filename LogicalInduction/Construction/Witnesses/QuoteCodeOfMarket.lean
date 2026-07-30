import LogicalInduction.Construction.Witnesses.ComputationDP
import LogicalInduction.Construction.Witnesses.LUVArithmetic

/-!
# Rational quote codes built from the market program

The self-referential theorems `thm:epr` (Expectations of Probabilities), `thm:er`
(Iterated Expectations), `thm:cee`, `thm:ceu`, `thm:ccee`, `thm:ref` (Introspection) and
`thm:st` (Self-Trust) each ask the market to price a sentence *quoting* one of its own
numbers.  `RationalQuoteCode` and `BooleanQuoteCode` (`QuotationAffine.lean`) are the
objects carrying such a quote.  This file constructs them from the certified market
program itself, so the semantic relation between the quoted syntax and the quantity it
names is derived rather than supplied by the caller.

* `arithmeticThresholdLUV_polyThresholdCodeSeq` discharges the `threshold_poly`
  obligation: one poly-fueled program emits the encoded quotation-atom threshold sentence
  `⌜value(n) > i/k⌝` from `⟨n,⟨k,i⟩⟩`, by the `gcdc`/`divmod1`/`ifzSel` recipe of
  `ComputableLUV.toLUV_polyThresholdCodes`.
* `RationalQuoteCode.ofComputable` gives a quote code to any total computable
  `[0,1]`-rational sequence; positive and negative completeness come from
  `BooleanQuoteCode.ofComputable` over the decidable comparison fiber.
* The `theorem…QuoteCode` definitions instantiate this at the constructed `LIA` market's
  own prices, expectations, deferred prices and confidence indicators.  The `…_closed`
  theorems are the corresponding paper endpoints with the reflection hypotheses
  discharged: each quoted LUV is built from the market program, and its exactness is the
  market certificate's `quote_exact`.
-/

namespace LogicalInduction

open Nat.Partrec (Code)
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open Filter Topology

/-! ## Part A — the threshold emitter for code-indexed quotation LUVs -/

@[simp] lemma arithmeticThresholdLUV_gt (code n : ℕ) (r : ℚ) :
    (arithmeticThresholdLUV code n).gt r =
      quoteAtom (Nat.pair code (Nat.pair n (Encodable.encode r))) := rfl

/-- The encoded quotation threshold sentence, in closed shell form: Foundation's
`Formula.atom` encoding is `pair 1 payload + 1`, and the payload is the tag-4 quotation
claim over the folded selector/input pair. -/
lemma encode_quoteAtom (w : ℕ) :
    Encodable.encode (quoteAtom w) =
      Nat.pair 1 (Nat.pair 4 (Nat.pair (Encodable.encode universalQuotePos)
        (Nat.pair (Encodable.encode universalQuoteNeg) w))) + 1 := rfl

/-- Reduced encoding of a natural-cast quotient:
`⌜(i:ℚ)/(k:ℚ)⌝ = pair (2·(i/gcd i k)) (k/gcd i k)` for `k ≠ 0`. -/
lemma encode_rat_natCast_div {i k : ℕ} (hk : k ≠ 0) :
    Encodable.encode ((i : ℚ) / (k : ℚ)) =
      Nat.pair (2 * (i / Nat.gcd i k)) (k / Nat.gcd i k) := by
  have hnum : ((i : ℚ) / (k : ℚ)).num = ((i / Nat.gcd i k : ℕ) : ℤ) :=
    ComputableLUV.natCast_div_num hk
  have hden : ((i : ℚ) / (k : ℚ)).den = k / Nat.gcd i k :=
    ComputableLUV.natCast_div_den hk
  rw [encode_rat_eq, hnum, hden, encode_int_natCast]

attribute [local irreducible] Nat.sqrt in
/-- One poly-fueled program emits the encoded quotation atom of selector `code` at day
`m.unpair.1` and mesh threshold `i/k` from the packed query `⟨n,⟨k,i⟩⟩`: runtime `gcdc`
reduction of the mesh rational, an `ifzSel` zero-denominator fallback, and the fixed atom
shell around the selector constant.  Factored so both the plain threshold LUV and the
indicator-product LUV (`thm:st`) can share it.
Paper node: `def:ec`, `thm:epr`, `thm:er`, `thm:st` -/
lemma quoteAtom_mesh_encode_polyFueled (code : ℕ) :
    ∃ c, PolyFueled c (fun m => Encodable.encode (quoteAtom (Nat.pair code
      (Nat.pair m.unpair.1 (Encodable.encode
        ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ))))))) := by
  obtain ⟨cg, hgcd⟩ := gcdc_polyFueled
  obtain ⟨cdm, hdm⟩ := divmod1_polyFueled
  obtain ⟨cad, had⟩ := addc_polyFueled
  -- Query `m = ⟨n, ⟨k, i⟩⟩`: day `n`, denominator `k`, numerator `i`.
  have hn := PolyFueled.left
  have hk := PolyFueled.left.comp PolyFueled.right
  have hi := PolyFueled.right.comp PolyFueled.right
  -- Raw reduced mesh pieces via `pred (gcd i k) + 1` (equational cleanup deferred).
  have gPF := hgcd.comp (hi.pair hk)
  have pgPF := predc_polyFueled.comp gPF
  have numPF := PolyFueled.left.comp (hdm.comp (pgPF.pair hi))
  have denPF := PolyFueled.left.comp (hdm.comp (pgPF.pair hk))
  have h2num := had.comp (numPF.pair numPF)
  -- Zero-denominator fallback `⌜(0:ℚ)⌝ = pair 0 1`.
  have meshPF := ifzSel_polyFueled.comp
    (((PolyFueled.const (Nat.pair 0 1)).pair (h2num.pair denPF)).pair hk)
  -- Fixed atom shell around the selector and day.
  have fullPF := ((PolyFueled.const 1).pair
    ((PolyFueled.const 4).pair
      ((PolyFueled.const (Encodable.encode universalQuotePos)).pair
        ((PolyFueled.const (Encodable.encode universalQuoteNeg)).pair
          ((PolyFueled.const code).pair (hn.pair meshPF)))))).succ_comp
  refine ⟨_, fullPF.of_eq (fun m => ?_)⟩
  rw [encode_quoteAtom]
  simp only [Nat.unpair_pair, ifzSelFn]
  by_cases hk0 : m.unpair.2.unpair.1 = 0
  · rw [if_pos hk0, hk0]
    norm_num
    rfl
  · rw [if_neg hk0]
    have hg : 0 < Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hk0)
    have hg1 : (Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1).pred + 1
        = Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.succ_pred_eq_of_pos hg
    rw [hg1, encode_rat_natCast_div hk0, two_mul]

/-- The `threshold_poly` obligation of a `RationalQuoteCode`, discharged for the universal
quotation schema at selector `code`.
Paper node: `def:ec`, `thm:epr`, `thm:er` -/
lemma arithmeticThresholdLUV_polyThresholdCodeSeq (code : ℕ) :
    LUV.PolyThresholdCodeSeq (fun n => arithmeticThresholdLUV code n) := by
  obtain ⟨c, hc⟩ := quoteAtom_mesh_encode_polyFueled code
  exact ⟨c, hc.of_eq (fun m => by rw [arithmeticThresholdLUV_gt])⟩

/-! ## Part B — a quote code for any total computable rational sequence -/

section
-- Primrec/Computable elaboration over ℚ product types loops `whnf` on `Nat.sqrt`
-- (pair/unpair unfolding); keep it opaque throughout Parts B–C.
attribute [local irreducible] Nat.sqrt

set_option maxHeartbeats 1000000 in
/-- The comparison fiber `⟨n, ⌜r⌝⟩ ↦ (r < value n)` of a computable rational sequence is a
computable predicate: rational order is `ratLE_prim`, the threshold decode is
`decodedQuotationRat_prim`, and the sequence itself is the hypothesis. -/
lemma decodedQuotationRat_lt_computablePred {value : ℕ → ℚ} (hvalue : Computable value) :
    ComputablePred fun input : ℕ =>
      decodedQuotationRat input.unpair.2 < value input.unpair.1 := by
  rw [ComputablePred.computable_iff]
  refine ⟨fun input =>
    !(decide (value input.unpair.1 ≤ decodedQuotationRat input.unpair.2)), ?_, ?_⟩
  · have h1 : Computable fun input : ℕ => decodedQuotationRat input.unpair.2 :=
      (decodedQuotationRat_prim.comp (Primrec.snd.comp Primrec.unpair)).to_comp
    have h2 : Computable fun input : ℕ => value input.unpair.1 :=
      hvalue.comp (Primrec.fst.comp Primrec.unpair).to_comp
    have hleB : Primrec fun p : ℚ × ℚ => decide (p.1 ≤ p.2) := ratLE_prim.decide
    -- The `( … : _)` ascription is load-bearing: it forces bottom-up elaboration of the
    -- composition, avoiding a `whnf` unification loop against the stated `decide` type.
    have hle : Computable fun input : ℕ =>
        decide (value input.unpair.1 ≤ decodedQuotationRat input.unpair.2) :=
      (hleB.to_comp.comp (h2.pair h1) : _)
    exact (Primrec.dom_bool Bool.not).to_comp.comp hle
  · funext input
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_le]

/-- Every total computable `[0,1]`-rational sequence has a `RationalQuoteCode`: name the
Boolean comparison decider by its program, and completeness is FFL weak representation of
the folded universal fibers (`BooleanQuoteCode.ofComputable`).  The `threshold_poly`
obligation is the Part-A emitter.
Paper node: `thm:epr` -/
noncomputable def RationalQuoteCode.ofComputable (T : ArithmeticTheory) [𝗥₀ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] {value : ℕ → ℚ} (hvalue : Computable value)
    (hmem : ∀ n, 0 ≤ value n ∧ value n ≤ 1) : RationalQuoteCode T value :=
  let b : BooleanQuoteCode T (fun input =>
      decodedQuotationRat input.unpair.2 < value input.unpair.1) :=
    BooleanQuoteCode.ofComputable (decodedQuotationRat_lt_computablePred hvalue)
  { code := b.code
    value_mem := hmem
    pos_complete := fun n r hr => b.pos_complete (Nat.pair n (Encodable.encode r))
      (by simpa [Nat.unpair_pair, decodedQuotationRat_encode] using hr)
    neg_complete := fun n r hr => b.neg_complete (Nat.pair n (Encodable.encode r))
      (by simp only [Nat.unpair_pair, decodedQuotationRat_encode]
          exact not_lt.mpr hr.le)
    threshold_poly := LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq
      (arithmeticThresholdLUV_polyThresholdCodeSeq b.code) }

/-! ## Part C — the market's own quotes are such a sequence -/

/-- The exact rational quote of a certified market program along computable day and
sentence-code streams is a total computable rational function. -/
lemma MarketComputation.quote_comp_computable {P : History} (market : MarketComputation P)
    {α : Type*} [Primcodable α] {d g : α → ℕ} (hd : Computable d) (hg : Computable g) :
    Computable fun a => market.quote (d a) (g a) := by
  have hin : Computable fun a => Nat.pair (d a) (g a) :=
    Primrec₂.natPair.to_comp.comp hd hg
  have heval : Partrec fun a => market.code.eval (Nat.pair (d a) (g a)) :=
    Nat.Partrec.Code.eval_part.comp (Computable.const market.code) hin
  have henc : Computable fun a => Encodable.encode (market.quote (d a) (g a)) :=
    heval.of_eq fun a => Part.eq_some_iff.mpr
      (by simpa [Nat.unpair_pair] using market.code_spec (Nat.pair (d a) (g a)))
  have hdec : Computable fun a =>
      (Encodable.decode (α := ℚ) (Encodable.encode (market.quote (d a) (g a)))).getD 0 :=
    Computable.option_getD (Computable.decode.comp henc) (Computable.const 0)
  exact hdec.of_eq fun a => by simp

/-- The certified market's exact rational quotes inherit the `[0,1]` price range. -/
lemma MarketComputation.quote_mem_Icc {P : History} (market : MarketComputation P)
    (n : ℕ) (φ : Sentence) :
    0 ≤ market.quote n (Encodable.encode φ) ∧ market.quote n (Encodable.encode φ) ≤ 1 := by
  have h := market.price_mem_Icc n φ
  rw [market.quote_exact n φ] at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-! ## Part D — the market's own expectations are also such a sequence -/

/-- Exact rational expectation of the LUV `X idx` at market day `day` (quotes from day
`day`, mesh the day's own grid `day + 1`): the rational value whose cast is the `def:e`
expectation `(X idx).expect P day`, computed through the market program's exact quotes.
The two indices separate the LUV selector from the evaluation day, which is what the
deferred-day theorems (`thm:cee`/`thm:st`) need. -/
def MarketComputation.expectQuoteAt {P : History} (market : MarketComputation P)
    (X : ℕ → LUV) (idx day : ℕ) : ℚ :=
  (∑ i ∈ Finset.range (day + 1),
      market.quote day
        (Encodable.encode ((X idx).gt ((i : ℚ) / ((day + 1 : ℕ) : ℚ))))) /
    ((day + 1 : ℕ) : ℚ)

/-- Exact rational day-`n` expectation of a varying LUV — the diagonal case. -/
def MarketComputation.expectQuote {P : History} (market : MarketComputation P)
    (X : ℕ → LUV) (n : ℕ) : ℚ :=
  market.expectQuoteAt X n n

/-- `expectQuoteAt` is exactly the real expectation, through the market certificate's
`quote_exact`. -/
lemma MarketComputation.expectQuoteAt_cast {P : History} (market : MarketComputation P)
    (X : ℕ → LUV) (idx day : ℕ) :
    (X idx).expect P day = (market.expectQuoteAt X idx day : ℝ) := by
  have hq : ∀ i : ℕ, P day ((X idx).gt ((i : ℚ) / ((day + 1 : ℕ) : ℚ))) =
      ((market.quote day
        (Encodable.encode ((X idx).gt ((i : ℚ) / ((day + 1 : ℕ) : ℚ)))) : ℚ) : ℝ) :=
    fun i => market.quote_exact day _
  simp only [LUV.expect, LUV.expectApprox, MarketComputation.expectQuoteAt]
  rw [Rat.cast_div, Rat.cast_sum]
  simp only [hq]
  push_cast
  ring

lemma MarketComputation.expectQuote_cast {P : History} (market : MarketComputation P)
    (X : ℕ → LUV) (n : ℕ) :
    (X n).expect P n = (market.expectQuote X n : ℝ) :=
  market.expectQuoteAt_cast X n n

/-- `expectQuoteAt` lands in `[0,1]`: an average of `[0,1]` quotes. -/
lemma MarketComputation.expectQuoteAt_mem_Icc {P : History} (market : MarketComputation P)
    (X : ℕ → LUV) (idx day : ℕ) :
    0 ≤ market.expectQuoteAt X idx day ∧ market.expectQuoteAt X idx day ≤ 1 := by
  unfold MarketComputation.expectQuoteAt
  have hterm : ∀ i ∈ Finset.range (day + 1),
      (0 : ℚ) ≤ market.quote day
          (Encodable.encode ((X idx).gt ((i : ℚ) / ((day + 1 : ℕ) : ℚ)))) ∧
        market.quote day
          (Encodable.encode ((X idx).gt ((i : ℚ) / ((day + 1 : ℕ) : ℚ)))) ≤ 1 :=
    fun i _ => market.quote_mem_Icc day _
  have hpos : (0 : ℚ) < ((day + 1 : ℕ) : ℚ) := by exact_mod_cast day.succ_pos
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i hi => (hterm i hi).1) hpos.le
  · rw [div_le_one hpos]
    calc (∑ i ∈ Finset.range (day + 1),
          market.quote day
            (Encodable.encode ((X idx).gt ((i : ℚ) / ((day + 1 : ℕ) : ℚ)))))
        ≤ ∑ _i ∈ Finset.range (day + 1), (1 : ℚ) :=
          Finset.sum_le_sum fun i hi => (hterm i hi).2
      _ = ((day + 1 : ℕ) : ℚ) := by simp

lemma MarketComputation.expectQuote_mem_Icc {P : History} (market : MarketComputation P)
    (X : ℕ → LUV) (n : ℕ) :
    0 ≤ market.expectQuote X n ∧ market.expectQuote X n ≤ 1 :=
  market.expectQuoteAt_mem_Icc X n n

/-- The natural-cast rational sequence is primitive recursive (closed encode form
`⌜(n:ℚ)⌝ = pair (n+n) 1`). -/
lemma ratNatCast_prim : Primrec fun n : ℕ => (n : ℚ) := by
  refine Primrec.encode_iff.mp ?_
  have h : Primrec fun n : ℕ => Nat.pair (n + n) 1 :=
    Primrec₂.natPair.comp (Primrec.nat_add.comp Primrec.id Primrec.id) (Primrec.const 1)
  exact h.of_eq fun n => by rw [encode_rat_natCast, two_mul]

set_option maxHeartbeats 1000000 in
/-- **`expectQuoteAt` is computable** (uncurried over `⟨idx, day⟩`).  Threshold codes
come from the LUV sequence's poly emitter, each cell quote from the market program, the
bounded sum by `Nat.rec` on the day, and the final average by `ratDiv_prim`. -/
lemma MarketComputation.expectQuoteAt_computable {P : History}
    (market : MarketComputation P)
    {X : ℕ → LUV} (hX : LUV.PolyThresholdCodeSeq X) :
    Computable fun a : ℕ × ℕ => market.expectQuoteAt X a.1 a.2 := by
  obtain ⟨cX, hcX⟩ := hX
  -- The threshold-code function of `⟨⟨idx, day⟩, i⟩`.
  have hpack : Computable fun z : (ℕ × ℕ) × ℕ =>
      Nat.pair z.1.1 (Nat.pair (z.1.2 + 1) z.2) :=
    Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.fst)
      (Primrec₂.natPair.to_comp.comp
        (Primrec.succ.to_comp.comp (Computable.snd.comp Computable.fst))
        Computable.snd)
  have hgt : Computable fun z : (ℕ × ℕ) × ℕ =>
      Encodable.encode ((X z.1.1).gt ((z.2 : ℚ) / ((z.1.2 + 1 : ℕ) : ℚ))) :=
    (hcX.primrec.to_comp.comp hpack).of_eq fun z => by simp [Nat.unpair_pair]
  -- The per-cell exact quote.
  have hcell : Computable fun z : (ℕ × ℕ) × ℕ =>
      market.quote z.1.2
        (Encodable.encode ((X z.1.1).gt ((z.2 : ℚ) / ((z.1.2 + 1 : ℕ) : ℚ)))) :=
    (market.quote_comp_computable (Computable.snd.comp Computable.fst) hgt : _)
  -- The bounded sum, by primitive recursion on the day.
  have hstepC : Computable fun q : (ℕ × ℕ) × (ℕ × ℚ) =>
      q.2.2 + market.quote q.1.2
        (Encodable.encode ((X q.1.1).gt ((q.2.1 : ℚ) / ((q.1.2 + 1 : ℕ) : ℚ)))) := by
    -- `( … : _)` ascriptions here and on `hcell` are load-bearing (see Part B note).
    have hc : Computable fun q : (ℕ × ℕ) × (ℕ × ℚ) =>
        market.quote q.1.2
          (Encodable.encode ((X q.1.1).gt ((q.2.1 : ℚ) / ((q.1.2 + 1 : ℕ) : ℚ)))) :=
      (hcell.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)) : _)
    exact (ratAdd_prim.to_comp.comp (Computable.snd.comp Computable.snd) hc : _)
  have hsum : Computable fun a : ℕ × ℕ => ∑ i ∈ Finset.range (a.2 + 1),
      market.quote a.2
        (Encodable.encode ((X a.1).gt ((i : ℚ) / ((a.2 + 1 : ℕ) : ℚ)))) := by
    have hrec := Computable.nat_rec (Primrec.succ.to_comp.comp Computable.snd)
      (Computable.const (0 : ℚ)) hstepC.to₂
    refine hrec.of_eq fun a => ?_
    have key : ∀ m : ℕ, (Nat.rec (motive := fun _ => ℚ) 0
        (fun i s => s + market.quote a.2
          (Encodable.encode ((X a.1).gt ((i : ℚ) / ((a.2 + 1 : ℕ) : ℚ))))) m) =
        ∑ i ∈ Finset.range m,
          market.quote a.2
            (Encodable.encode ((X a.1).gt ((i : ℚ) / ((a.2 + 1 : ℕ) : ℚ)))) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, ← ih]
    exact key (a.2 + 1)
  -- The final average.
  exact ((ratDiv_prim.to_comp.comp hsum
    (ratNatCast_prim.to_comp.comp (Primrec.succ.to_comp.comp Computable.snd)) : _) :
    Computable fun a : ℕ × ℕ => market.expectQuoteAt X a.1 a.2)

/-- Diagonal corollary: the day-`n` expectation sequence is computable.
Paper node: `thm:er` -/
lemma MarketComputation.expectQuote_computable {P : History}
    (market : MarketComputation P)
    {X : ℕ → LUV} (hX : LUV.PolyThresholdCodeSeq X) :
    Computable (market.expectQuote X) :=
  ((market.expectQuoteAt_computable hX).comp
    (Computable.id.pair Computable.id)).of_eq fun n => rfl

/-! ## Part E — the ctsInd-composed confidence value and the indicator product
(`thm:st`'s reflection data, constructed) -/

/-- Rational continuous threshold indicator: the exact value whose cast is
`ctsInd δ (q:ℝ) (p:ℝ)`. -/
def ratCtsInd (δ q p : ℚ) : ℚ := min 1 (max 0 ((q - p) / δ))

lemma ratCtsInd_cast (δ q p : ℚ) :
    ctsInd δ (q : ℝ) (p : ℝ) = (ratCtsInd δ q p : ℝ) := by
  unfold ctsInd ratCtsInd
  push_cast
  rfl

lemma ratCtsInd_mem_Icc (δ q p : ℚ) : 0 ≤ ratCtsInd δ q p ∧ ratCtsInd δ q p ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left 0 _), min_le_left _ _⟩

/-- A poly-coded rational sequence is computable (decode the emitted code). -/
lemma PolyRatCodes.computable {q : ℕ → ℚ} (h : PolyRatCodes q) : Computable q := by
  obtain ⟨c, hc⟩ := h
  exact (Computable.option_getD (Computable.decode.comp hc.primrec.to_comp)
    (Computable.const 0)).of_eq fun n => by simp

/-- `ratCtsInd` is computable in its packed arguments, from the public rational
primitives (`min a b = a + b - max a b` avoids any Boolean branch). -/
lemma ratCtsInd_computable :
    Computable fun z : ℚ × ℚ × ℚ => ratCtsInd z.1 z.2.1 z.2.2 := by
  have hδ : Computable fun z : ℚ × ℚ × ℚ => z.1 := Computable.fst
  have hq : Computable fun z : ℚ × ℚ × ℚ => z.2.1 :=
    Computable.fst.comp Computable.snd
  have hp : Computable fun z : ℚ × ℚ × ℚ => z.2.2 :=
    Computable.snd.comp Computable.snd
  have hsub : Computable fun z : ℚ × ℚ × ℚ => z.2.1 + (-1) * z.2.2 :=
    (ratAdd_prim.to_comp.comp hq
      (ratMul_prim.to_comp.comp (Computable.const (-1)) hp) : _)
  have hdiv : Computable fun z : ℚ × ℚ × ℚ => (z.2.1 + (-1) * z.2.2) / z.1 :=
    (ratDiv_prim.to_comp.comp hsub hδ : _)
  have hmax : Computable fun z : ℚ × ℚ × ℚ =>
      max 0 ((z.2.1 + (-1) * z.2.2) / z.1) :=
    (ratMax_prim.to_comp.comp (Computable.const 0) hdiv : _)
  have hmaxTop : Computable fun z : ℚ × ℚ × ℚ =>
      max 1 (max 0 ((z.2.1 + (-1) * z.2.2) / z.1)) :=
    (ratMax_prim.to_comp.comp (Computable.const 1) hmax : _)
  have hsum : Computable fun z : ℚ × ℚ × ℚ =>
      1 + max 0 ((z.2.1 + (-1) * z.2.2) / z.1) :=
    (ratAdd_prim.to_comp.comp (Computable.const 1) hmax : _)
  have hfin : Computable fun z : ℚ × ℚ × ℚ =>
      (1 + max 0 ((z.2.1 + (-1) * z.2.2) / z.1)) +
        (-1) * max 1 (max 0 ((z.2.1 + (-1) * z.2.2) / z.1)) :=
    (ratAdd_prim.to_comp.comp hsum
      (ratMul_prim.to_comp.comp (Computable.const (-1)) hmaxTop) : _)
  refine hfin.of_eq fun z => ?_
  unfold ratCtsInd
  have hmm := min_add_max (1 : ℚ) (max 0 ((z.2.1 - z.2.2) / z.1))
  have harg : z.2.1 + (-1) * z.2.2 = z.2.1 - z.2.2 := by ring
  rw [harg]
  linarith

/-- The indicator-product LUV `1(φ n) · value`: thresholds are `⊤` below zero and the
conjunction `φ n ⋏ ⌜value > r⌝` at nonnegative `r`.  Its completed-theory value is the
world's payout on `φ n` times the represented rational — the quoted product `thm:st`
needs. -/
noncomputable def indicatorProductLUV {T : ArithmeticTheory} {value : ℕ → ℚ}
    (q : RationalQuoteCode T value) (φ : ℕ → Sentence) (n : ℕ) : LUV where
  gt r := if r < 0 then ⊤ else (φ n ⋏ (q.luv n).gt r)

@[simp] lemma indicatorProductLUV_gt {T : ArithmeticTheory} {value : ℕ → ℚ}
    (q : RationalQuoteCode T value) (φ : ℕ → Sentence) (n : ℕ) (r : ℚ) :
    (indicatorProductLUV q φ n).gt r =
      if r < 0 then ⊤ else (φ n ⋏ (q.luv n).gt r) := rfl

/-- Every p.c. world holds `⊤` (`⊤ = ⊥ 🡒 ⊥` and Boolean semantics is structural). -/
lemma PCWorld.holds_top (v : PCWorld) : v.Holds (⊤ : Sentence) := fun h => h

/-- **The product law**: completed-theory worlds value the indicator product at exactly
`payout(φ n) · value n`.
Paper node: `thm:st` -/
lemma indicatorProductLUV_valuesAt {DP : DeductiveProcess} {T : ArithmeticTheory}
    {value : ℕ → ℚ} (Q : QuotationTheoryPresentation DP T)
    (q : RationalQuoteCode T value) (φ : ℕ → Sentence) (n : ℕ)
    (v : PCWorld) (hv : v.ConsistentWithTheory DP) :
    v.ValuesAt (indicatorProductLUV q φ n) (v.payout (φ n) * (value n : ℝ)) := by
  obtain ⟨h0, h1, hthr⟩ := RationalQuoteCode.reflected Q q n v hv
  by_cases hφv : v.Holds (φ n)
  · have hpay : v.payout (φ n) = 1 := if_pos hφv
    rw [hpay, one_mul]
    refine ⟨h0, h1, fun r => ⟨?_, ?_⟩⟩
    · intro hr
      rw [indicatorProductLUV_gt]
      by_cases hr0 : r < 0
      · rw [if_pos hr0]; exact PCWorld.holds_top v
      · rw [if_neg hr0]
        exact (PCWorld.holds_and v _ _).mpr ⟨hφv, (hthr r).1 hr⟩
    · intro hr
      rw [indicatorProductLUV_gt]
      have hr0 : ¬ r < 0 := by
        have hrR : (0 : ℝ) < (r : ℝ) := lt_of_le_of_lt h0 hr
        have : (0 : ℚ) < r := by exact_mod_cast hrR
        exact not_lt.mpr this.le
      rw [if_neg hr0]
      intro hcon
      exact (hthr r).2 hr ((PCWorld.holds_and v _ _).mp hcon).2
  · have hpay : v.payout (φ n) = 0 := if_neg hφv
    rw [hpay, zero_mul]
    refine ⟨le_refl 0, zero_le_one, fun r => ⟨?_, ?_⟩⟩
    · intro hr
      rw [indicatorProductLUV_gt, if_pos (by exact_mod_cast hr : r < 0)]
      exact PCWorld.holds_top v
    · intro hr
      have hr0 : ¬ r < 0 := by
        have : (0 : ℚ) < r := by exact_mod_cast hr
        exact not_lt.mpr this.le
      rw [indicatorProductLUV_gt, if_neg hr0]
      intro hcon
      exact hφv ((PCWorld.holds_and v _ _).mp hcon).1

/-- The encoded `⋏`-node shell of Foundation's propositional formulas. -/
lemma encode_and (p q : Sentence) :
    Encodable.encode (p ⋏ q) =
      Nat.pair 3 (Nat.pair (Encodable.encode p) (Encodable.encode q)) + 1 := rfl

/-- The indicator product's threshold family is polynomially codeable: the fixed
`⋏`-shell around the sentence's poly code and the shared quotation-atom emitter (mesh
thresholds are nonnegative, so the `⊤` branch is never emitted).
Paper node: `def:ec`, `thm:st` -/
lemma indicatorProductLUV_polyThresholdCodeSeq {T : ArithmeticTheory} {value : ℕ → ℚ}
    (q : RationalQuoteCode T value) {φ : ℕ → Sentence} (hφ : PolySentenceCodes φ) :
    LUV.PolyThresholdCodeSeq (fun n => indicatorProductLUV q φ n) := by
  obtain ⟨cφ, hcφ⟩ := hφ
  obtain ⟨ca, hca⟩ := quoteAtom_mesh_encode_polyFueled q.code
  have hφAt := hcφ.comp PolyFueled.left
  have fullPF := ((PolyFueled.const 3).pair (hφAt.pair hca)).succ_comp
  refine ⟨_, fullPF.of_eq (fun m => ?_)⟩
  have hmesh0 : ¬ ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ)) < 0 :=
    not_lt.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  rw [indicatorProductLUV_gt, if_neg hmesh0, encode_and]
  rfl

/-- A deferral function is (unclamped) computable: its certificate's clocked runs are
sound for the unbounded semantics. -/
lemma DeferralFunction.computable (f : DeferralFunction) : Computable f.f := by
  obtain ⟨a, k, hf⟩ := f.fueled
  have hpart : Partrec fun n => f.code.eval n :=
    Nat.Partrec.Code.eval_part.comp (Computable.const f.code) Computable.id
  exact hpart.of_eq fun n => Part.eq_some_iff.mpr
    (Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr (hf n)))

section
variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- The canonical quote code of the constructed `LIA` market's own prices along an
efficiently codeable sentence sequence.  No caller-supplied semantic relation: the value
program is the market program, and range comes from its certificate.
Paper node: `thm:epr` -/
noncomputable def theoremPriceQuoteCode (φ : ℕ → Sentence) (hφ : PolySentenceCodes φ) :
    RationalQuoteCode T (fun n =>
      (theoremMarketComputation T).quote n (Encodable.encode (φ n))) :=
  RationalQuoteCode.ofComputable T
    ((theoremMarketComputation T).quote_comp_computable Computable.id
      hφ.choose_spec.primrec.to_comp)
    (fun n => (theoremMarketComputation T).quote_mem_Icc n (φ n))

/-- **`thm:epr`, closed form over the constructed `LIA`** — no reflection hypotheses.
For every efficiently codeable sentence sequence, the market's price agrees asymptotically
with its own expectation of the *constructed* quoted-price LUV.  The quote object is
`theoremPriceQuoteCode`; its exactness is the market certificate's `quote_exact`, so the
only remaining hypotheses are the sequence and its poly codes.
Paper node: `thm:epr` -/
theorem lic_expectations_of_probabilities_closed
    (φ : ℕ → Sentence) (hφ : PolySentenceCodes φ) :
    (fun n => liaHistory (theoremDP T) n (φ n)) ≈ₙ
      fun n => ((theoremPriceQuoteCode T φ hφ).luv n).expect (liaHistory (theoremDP T)) n :=
  lic_expectations_of_probabilities_ofCode_unconditional (T := T) φ
    (RpnSentenceCodes.ofPolySentenceCodes hφ)
    (theoremPriceQuoteCode T φ hφ)
    (fun n => (theoremMarketComputation T).quote_exact n (φ n))

/-- The canonical quote code of the constructed `LIA` market's own day-`n` expectations of
an efficiently codeable LUV sequence.  The value program is the expectation compiler over
the market program; range and exactness come from its certificate.
Paper node: `thm:er` -/
noncomputable def theoremExpectationQuoteCode (X : ℕ → LUV)
    (hX : LUV.PolyThresholdCodeSeq X) :
    RationalQuoteCode T ((theoremMarketComputation T).expectQuote X) :=
  RationalQuoteCode.ofComputable T
    ((theoremMarketComputation T).expectQuote_computable hX)
    ((theoremMarketComputation T).expectQuote_mem_Icc X)

/-- The future-quote code: `value n = quote (f n) ⌜φ n⌝`, the market's own deferred-day
price of the day-`n` sentence.  No caller-supplied semantic relation.
Paper node: `thm:ceu` -/
noncomputable def theoremFutureQuoteCode (f : DeferralFunction)
    (φ : ℕ → Sentence) (hφ : PolySentenceCodes φ) :
    RationalQuoteCode T (fun n =>
      (theoremMarketComputation T).quote (f.f n) (Encodable.encode (φ n))) :=
  RationalQuoteCode.ofComputable T
    ((theoremMarketComputation T).quote_comp_computable f.computable
      hφ.choose_spec.primrec.to_comp)
    (fun n => (theoremMarketComputation T).quote_mem_Icc (f.f n) (φ n))

/-- **`thm:ceu` (no expected net update), closed form over the constructed `LIA`** — no
reflection hypotheses.  The quoted future-price LUV is constructed from the market
program itself; only the sentence sequence, its poly codes, and the deferral function
remain.
Paper node: `thm:ceu` -/
theorem lic_no_expected_net_update_closed
    (f : DeferralFunction)
    (φ : ℕ → Sentence) (hφ : PolySentenceCodes φ) :
    (fun n ↦ liaHistory (theoremDP T) n (φ n)) ≈ₙ
      fun n ↦ ((theoremFutureQuoteCode T f φ hφ).luv n).expect
        (liaHistory (theoremDP T)) n :=
  lic_no_expected_net_update_ofRepresentation_unconditional (T := T) f φ
    ((theoremFutureQuoteCode T f φ hφ).luv)
    (RpnSentenceCodes.ofPolySentenceCodes hφ)
    (theoremFutureQuoteCode T f φ hφ).poly
    (fun n v hv => by
      have h := RationalQuoteCode.reflected (quotationPresentation T)
        (theoremFutureQuoteCode T f φ hφ) n v hv
      rwa [← (theoremMarketComputation T).quote_exact (f.f n) (φ n)] at h)

/-- The deferred-expectation quote code: `value n = expectQuoteAt X n (f n)`, the
market's own day-`f n` expectation of the day-`n` LUV.
Paper node: `thm:cee` -/
noncomputable def theoremDeferredExpectationQuoteCode (f : DeferralFunction)
    (X : ℕ → LUV) (hX : LUV.PolyThresholdCodeSeq X) :
    RationalQuoteCode T (fun n =>
      (theoremMarketComputation T).expectQuoteAt X n (f.f n)) :=
  -- The `( … : _)` ascription is load-bearing (see the Part B note).
  have hcomp : Computable fun n =>
      (theoremMarketComputation T).expectQuoteAt X n (f.f n) :=
    (((theoremMarketComputation T).expectQuoteAt_computable hX).comp
      (Computable.id.pair f.computable) : _)
  RationalQuoteCode.ofComputable T hcomp
    (fun n => (theoremMarketComputation T).expectQuoteAt_mem_Icc X n (f.f n))

/-- **`thm:cee` (expected future expectations), closed form over the constructed `LIA`**
— the reflection data is constructed from the market program; only the source LUV
sequence, its poly codes, its own theory-valuedness (`source_valued`, the paper's premise
that `X` is a genuine LUV of the theory), and the deferral function remain.
Paper node: `thm:cee` -/
theorem lic_expected_future_expectations_closed
    (f : DeferralFunction)
    (X : ℕ → LUV) (hX : LUV.PolyThresholdCodeSeq X)
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory (theoremDP T) →
      ∃ x, v.ValuesAt (X n) x) :
    (fun n ↦ (X n).expect (liaHistory (theoremDP T)) n) ≈ₙ
      fun n ↦ ((theoremDeferredExpectationQuoteCode T f X hX).luv n).expect
        (liaHistory (theoremDP T)) n :=
  lic_expected_future_expectations_ofRepresentation_unconditional (T := T) f X
    ((theoremDeferredExpectationQuoteCode T f X hX).luv)
    (LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq hX)
    (theoremDeferredExpectationQuoteCode T f X hX).poly source_valued
    (fun n v hv => by
      have h := RationalQuoteCode.reflected (quotationPresentation T)
        (theoremDeferredExpectationQuoteCode T f X hX) n v hv
      rwa [← (theoremMarketComputation T).expectQuoteAt_cast X n (f.f n)] at h)

/-- **`thm:er`, closed form over the constructed `LIA`** — no reflection hypotheses.
For every efficiently codeable LUV sequence, the market's expectation agrees
asymptotically with its expectation of the *constructed* quoted-expectation LUV.  Only
the LUV sequence and its poly threshold codes remain.
Paper node: `thm:er` -/
theorem lic_iterated_expectations_closed
    (X : ℕ → LUV) (hX : LUV.PolyThresholdCodeSeq X) :
    (fun n => (X n).expect (liaHistory (theoremDP T)) n) ≈ₙ
      fun n => ((theoremExpectationQuoteCode T X hX).luv n).expect
        (liaHistory (theoremDP T)) n :=
  lic_iterated_expectations_ofCode_unconditional (T := T) X
    (LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq hX)
    (theoremExpectationQuoteCode T X hX)
    ((theoremMarketComputation T).expectQuote_cast X)

/-- The confidence quote code for `thm:st`: the market's own continuous indicator of its
deferred-day price against the target probability,
`value n = ratCtsInd (δ n) (quote (f n) ⌜φ n⌝) (p n)`.

The threshold `p` is P-generable (`def:ece`), exactly as in the paper: the emitter recovers
a program for `p` from the feature presentation by parsing the emitted serialization
(`RpnSpliceStream.feature_primrec`) and evaluating it against this market
(`PGenerableRat.computable`).
Paper node: `thm:st` -/
noncomputable def theoremConfidenceQuoteCode (f : DeferralFunction)
    (φ : ℕ → Sentence) (hφ : PolySentenceCodes φ) (δ p : ℕ → ℚ)
    (hδ : PolyRatCodes δ) (hp : PGenerableRat (liaHistory (theoremDP T)) p) :
    RationalQuoteCode T (fun n => ratCtsInd (δ n)
      ((theoremMarketComputation T).quote (f n) (Encodable.encode (φ n))) (p n)) :=
  have hquote : Computable fun n =>
      (theoremMarketComputation T).quote (f n) (Encodable.encode (φ n)) :=
    ((theoremMarketComputation T).quote_comp_computable f.computable
      hφ.choose_spec.primrec.to_comp : _)
  have hval : Computable fun n => ratCtsInd (δ n)
      ((theoremMarketComputation T).quote (f n) (Encodable.encode (φ n))) (p n) :=
    (ratCtsInd_computable.comp (hδ.computable.pair
      (hquote.pair (hp.computable (theoremMarketComputation T)))) : _)
  RationalQuoteCode.ofComputable T hval (fun n => ratCtsInd_mem_Icc _ _ _)

/-- Cast identity for the confidence value against the real market. -/
lemma theoremConfidence_value_cast (f : DeferralFunction) (φ : ℕ → Sentence)
    (δ p : ℕ → ℚ) (n : ℕ) :
    ctsInd (δ n) (liaHistory (theoremDP T) (f n) (φ n)) ((p n : ℝ)) =
      ((ratCtsInd (δ n) ((theoremMarketComputation T).quote (f n)
        (Encodable.encode (φ n))) (p n) : ℚ) : ℝ) := by
  rw [(theoremMarketComputation T).quote_exact (f n) (φ n), ratCtsInd_cast]

set_option maxHeartbeats 1000000 in
/-- The interval quote code for `thm:ref`: one Boolean decider names the fact
`a n < Pₙ(φ n) < b n`, computed from the market program's exact rational quote.  This is
the introspection target sentence, constructed with no caller-supplied truth relation.
Paper node: `thm:ref` -/
noncomputable def theoremIntervalQuoteCode (φ : ℕ → Sentence) (hφ : PolySentenceCodes φ)
    (a b : ℕ → ℚ) (ha : PolyRatCodes a) (hb : PolyRatCodes b) :
    BooleanQuoteCode T (fun n ↦
      (a n : ℝ) < liaHistory (theoremDP T) n (φ n) ∧
        liaHistory (theoremDP T) n (φ n) < (b n : ℝ)) := by
  refine BooleanQuoteCode.ofComputable ?_
  rw [ComputablePred.computable_iff]
  refine ⟨fun n =>
    (!(decide ((theoremMarketComputation T).quote n (Encodable.encode (φ n)) ≤ a n))) &&
      (!(decide (b n ≤ (theoremMarketComputation T).quote n (Encodable.encode (φ n))))),
    ?_, ?_⟩
  · have hq : Computable fun n =>
        (theoremMarketComputation T).quote n (Encodable.encode (φ n)) :=
      ((theoremMarketComputation T).quote_comp_computable Computable.id
        hφ.choose_spec.primrec.to_comp : _)
    have hleB : Primrec fun z : ℚ × ℚ => decide (z.1 ≤ z.2) := ratLE_prim.decide
    have h1 : Computable fun n => decide
        ((theoremMarketComputation T).quote n (Encodable.encode (φ n)) ≤ a n) :=
      (hleB.to_comp.comp (hq.pair ha.computable) : _)
    have h2 : Computable fun n => decide
        (b n ≤ (theoremMarketComputation T).quote n (Encodable.encode (φ n))) :=
      (hleB.to_comp.comp (hb.computable.pair hq) : _)
    have hn1 := (Primrec.dom_bool Bool.not).to_comp.comp h1
    have hn2 := (Primrec.dom_bool Bool.not).to_comp.comp h2
    exact ((Primrec.dom_bool₂ Bool.and).to_comp.comp hn1 hn2 : _)
  · funext n
    rw [(theoremMarketComputation T).quote_exact n (φ n)]
    simp only [eq_iff_iff, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, not_le, Rat.cast_lt]

/-- **`thm:ref` (introspection), closed form over the constructed `LIA`** — the interval
quote is constructed from the market program; the remaining hypotheses are the paper's
own (`a`/`b` e.c. interval bounds and their market-generated feature presentations, the
vanishing width, and the range side conditions).
Paper node: `thm:ref` -/
theorem lic_introspection_closed
    (φ : ℕ → Sentence) (hφ : PolySentenceCodes φ) (a b δ : ℕ → ℚ)
    (ha : PolyRatCodes a) (hb : PolyRatCodes b)
    (lowerFeature : ℕ → EF)
    (hlower : GeneratedRatFeature (liaHistory (theoremDP T)) a lowerFeature)
    (upperFeature : ℕ → EF)
    (hupper : GeneratedRatFeature (liaHistory (theoremDP T)) b upperFeature)
    (hδ : PolyRatCodes δ) (hδinv : PolyRatCodes (fun n ↦ 1 / δ n))
    (hδpos : ∀ n, 0 < δ n)
    (hδzero : Tendsto (fun n ↦ (δ n : ℝ)) atTop (𝓝 0))
    (hab : ∀ n, 0 ≤ a n ∧ a n ≤ 1 ∧ 0 ≤ b n ∧ b n ≤ 1) :
    ∃ ε : ℕ → ℚ, (∀ n, 0 < ε n) ∧ Tendsto (fun n ↦ (ε n : ℝ)) atTop (𝓝 0) ∧
      ∀ n,
        (((a n : ℝ) + δ n < liaHistory (theoremDP T) n (φ n) ∧
            liaHistory (theoremDP T) n (φ n) < (b n : ℝ) - δ n) →
          1 - (ε n : ℝ) < liaHistory (theoremDP T) n
            ((theoremIntervalQuoteCode T φ hφ a b ha hb).sentence n)) ∧
        ((¬ ((a n : ℝ) - δ n < liaHistory (theoremDP T) n (φ n) ∧
              liaHistory (theoremDP T) n (φ n) < (b n : ℝ) + δ n)) →
          liaHistory (theoremDP T) n
            ((theoremIntervalQuoteCode T φ hφ a b ha hb).sentence n) < (ε n : ℝ)) :=
  lic_introspection_ofCode_unconditional (T := T) φ
    (RpnSentenceCodes.ofPolySentenceCodes hφ) a b δ lowerFeature hlower
    upperFeature hupper hδ hδinv hδpos hδzero hab
    (theoremIntervalQuoteCode T φ hφ a b ha hb)

/-- **`thm:st` (self-trust), closed form over the constructed `LIA`** — no reflection
hypotheses.  Both quoted LUVs are constructed: `B` is the confidence quote code of the
market's own deferred-day price, and `A` is its indicator product with `φ n`.  Only the
sentence sequence, the deferral function, and the threshold data remain.

The threshold `p` is P-generable (`def:ece`), matching the paper: the quote code recovers
a program for `p` from the feature presentation itself (`PGenerableRat.computable`).  An
e.c. rational sequence is the constant-feature special case — supply
`⟨ratCodeFeature p, ratCodeFeature_generated _ p hp⟩` for `hp : PolyRatCodes p`.
Paper node: `thm:st` -/
theorem lic_self_trust_closed
    (f : DeferralFunction)
    (φ : ℕ → Sentence) (δ p : ℕ → ℚ)
    (delta_pos : ∀ n, 0 < δ n) (probability_mem : ∀ n, 0 ≤ p n ∧ p n ≤ 1)
    (hφ : PolySentenceCodes φ) (hδ : PolyRatCodes δ)
    (hδinv : PolyRatCodes (fun n ↦ 1 / δ n))
    (hp : PGenerableRat (liaHistory (theoremDP T)) p) :
    (fun n ↦ (indicatorProductLUV (theoremConfidenceQuoteCode T f φ hφ δ p hδ hp) φ n).expect
        (liaHistory (theoremDP T)) n) ≳ₙ
      fun n ↦ (p n : ℝ) *
        ((theoremConfidenceQuoteCode T f φ hφ δ p hδ hp).luv n).expect
          (liaHistory (theoremDP T)) n := by
  refine lic_self_trust_ofRepresentation_unconditional (T := T) f φ δ p
    (fun n => indicatorProductLUV (theoremConfidenceQuoteCode T f φ hφ δ p hδ hp) φ n)
    (theoremConfidenceQuoteCode T f φ hφ δ p hδ hp).luv
    delta_pos probability_mem (RpnSentenceCodes.ofPolySentenceCodes hφ) hδ hδinv
    hp.choose hp.choose_spec
    (LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq
      (indicatorProductLUV_polyThresholdCodeSeq _ hφ))
    (theoremConfidenceQuoteCode T f φ hφ δ p hδ hp).poly
    (fun n v hv => ?_) (fun n v hv => ?_)
  · have h := RationalQuoteCode.reflected (quotationPresentation T)
      (theoremConfidenceQuoteCode T f φ hφ δ p hδ hp) n v hv
    rwa [← theoremConfidence_value_cast T f φ δ p n] at h
  · have h := indicatorProductLUV_valuesAt (quotationPresentation T)
      (theoremConfidenceQuoteCode T f φ hφ δ p hδ hp) φ n v hv
    rwa [← theoremConfidence_value_cast T f φ δ p n] at h

/-! ## Part F — the weighted conditional (`thm:ccee`), indicator-source closed form

A closed form for fully general caller sources is out of reach for a structural reason:
the scaled LUV's mesh threshold must contain the sentence `X.gt (r / w (f n))` — a finite
Boolean combination of `X` thresholds only jumps at the thresholds it uses — so its
emitter would have to *compute* `w (f n)` within fuel polynomial in `n`, exactly what
`def:deferralfunc` withholds (the paper's trader likewise never evaluates `w_{f(n)}` on
day `n`; it names it inside quoted syntax).  The closed instance below is therefore the
paper's motivating conditional-probability case: the source is a relational indicator
family, the left quoted product is the `thm:st` indicator-product over a quote code
*naming* the `w ∘ f` program, and the right quote names the market's own deferred
weighted expectation program. -/

/-- Quote code naming the deferred-weight program `n ↦ w (f n)`: the quotation atom
quotes the program, so deferral costs nothing at strategy-emission time.  The weight is
P-generable (`def:ece`); its program comes from the feature presentation
(`PGenerableRat.computable`).
Paper node: `thm:ccee` -/
noncomputable def theoremDeferredWeightQuoteCode (f : DeferralFunction) (w : ℕ → ℚ)
    (hw : PGenerableRat (liaHistory (theoremDP T)) w)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) :
    RationalQuoteCode T (fun n => w (f n)) :=
  RationalQuoteCode.ofComputable T
    ((hw.computable (theoremMarketComputation T)).comp f.computable)
    (fun n => weight_mem (f n))

/-- Quote code for the market's own deferred weighted expectation
`n ↦ 𝔼_{f n}(X n) · w (f n)`, in exact rational form.
Paper node: `thm:ccee` -/
noncomputable def theoremConditionalExpectationQuoteCode (f : DeferralFunction)
    (X : ℕ → LUV) (hX : LUV.PolyThresholdCodeSeq X) (w : ℕ → ℚ)
    (hw : PGenerableRat (liaHistory (theoremDP T)) w)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) :
    RationalQuoteCode T (fun n =>
      (theoremMarketComputation T).expectQuoteAt X n (f.f n) * w (f.f n)) :=
  -- The `( … : _)` ascriptions are load-bearing (see the Part B note).
  have hexp : Computable fun n =>
      (theoremMarketComputation T).expectQuoteAt X n (f.f n) :=
    (((theoremMarketComputation T).expectQuoteAt_computable hX).comp
      (Computable.id.pair f.computable) : _)
  have hval : Computable fun n =>
      (theoremMarketComputation T).expectQuoteAt X n (f.f n) * w (f.f n) :=
    (ratMul_prim.to_comp.comp hexp
      ((hw.computable (theoremMarketComputation T)).comp f.computable) : _)
  RationalQuoteCode.ofComputable T hval
    (fun n => by
      obtain ⟨he0, he1⟩ :=
        (theoremMarketComputation T).expectQuoteAt_mem_Icc X n (f.f n)
      obtain ⟨hw0, hw1⟩ := weight_mem (f.f n)
      exact ⟨mul_nonneg he0 hw0, by nlinarith⟩)

/-- **`thm:ccee` (no expected net update under conditionals), closed form over the
constructed `LIA`** — the paper's conditional-probability instance, with both quoted
products constructed.  The source `X` is supplied by its indicator relation to `φ` rather
than as a concrete LUV term; `Z` is its indicator product with the deferred-weight quote
code, and `Z'` the quote of the market's own deferred weighted expectation.  Only the
sentence sequence, the source family and its indicator linkage, the weight data, and the
deferral function remain.
Paper node: `thm:ccee` -/
theorem lic_no_expected_net_update_conditional_closed
    (f : DeferralFunction)
    (φ : ℕ → Sentence) (hφ : PolySentenceCodes φ)
    (X : ℕ → LUV) (hX : LUV.PolyThresholdCodeSeq X)
    (hind : ∀ n, (X n).IsIndicator (φ n) (theoremDP T))
    (w : ℕ → ℚ) (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat (liaHistory (theoremDP T)) w) :
    (fun n ↦ (indicatorProductLUV
        (theoremDeferredWeightQuoteCode T f w weight_generable weight_mem) φ n).expect
          (liaHistory (theoremDP T)) n) ≈ₙ
      fun n ↦ ((theoremConditionalExpectationQuoteCode T f X hX w weight_generable
        weight_mem).luv n).expect (liaHistory (theoremDP T)) n := by
  refine lic_no_expected_net_update_conditional_ofRepresentation_unconditional (T := T)
    f X
    (fun n => indicatorProductLUV
      (theoremDeferredWeightQuoteCode T f w weight_generable weight_mem) φ n)
    ((theoremConditionalExpectationQuoteCode T f X hX w weight_generable weight_mem).luv)
    w weight_mem weight_generable (LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq hX)
    (LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq
      (indicatorProductLUV_polyThresholdCodeSeq _ hφ))
    (theoremConditionalExpectationQuoteCode T f X hX w weight_generable weight_mem).poly
    (fun n v hv => ⟨v.payout (φ n), (hind n).valuesAt (hv n)⟩)
    (fun n v hv x hx => ?_) (fun n v hv => ?_)
  · have hxeq : x = v.payout (φ n) := hx.eq ((hind n).valuesAt (hv n))
    have h := indicatorProductLUV_valuesAt (quotationPresentation T)
      (theoremDeferredWeightQuoteCode T f w weight_generable weight_mem) φ n v hv
    rwa [hxeq]
  · have h := RationalQuoteCode.reflected (quotationPresentation T)
      (theoremConditionalExpectationQuoteCode T f X hX w weight_generable weight_mem) n v hv
    rwa [Rat.cast_mul,
      ← (theoremMarketComputation T).expectQuoteAt_cast X n (f.f n)] at h

end

end

#print axioms arithmeticThresholdLUV_polyThresholdCodeSeq
#print axioms RationalQuoteCode.ofComputable
#print axioms lic_expectations_of_probabilities_closed
#print axioms MarketComputation.expectQuote_computable
#print axioms lic_iterated_expectations_closed
#print axioms lic_no_expected_net_update_conditional_closed

end LogicalInduction
