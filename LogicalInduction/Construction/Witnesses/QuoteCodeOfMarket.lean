import LogicalInduction.Construction.Witnesses.ComputationDP
import LogicalInduction.Construction.Witnesses.LUVArithmetic

/-!
# Constructed rational quote codes — closing the epr/er reflection seam

`RationalQuoteCode` (QuotationAffine.lean) has until now only been *consumed*: every
`thm:epr`/`thm:er` endpoint took the quote object and its exactness as caller hypotheses.
This file constructs it, the way `parameterizedDiagonalQuoteCodeOfMarket` already does for
the paradox-resistance diagonal: from the certified market program itself, with no
caller-supplied semantic relation.

* `arithmeticThresholdLUV_polyThresholdCodeSeq` — the first discharge of a
  `RationalQuoteCode.threshold_poly` obligation: one poly-fueled program emits the encoded
  quotation-atom threshold sentence `⌜value(n) > i/k⌝` from `⟨n,⟨k,i⟩⟩`, by the
  `gcdc`/`divmod1`/`ifzSel` recipe of `ComputableLUV.toLUV_polyThresholdCodes`.
* `RationalQuoteCode.ofComputable` — any total computable `[0,1]`-rational sequence has a
  quote code; positive/negative completeness comes from `BooleanQuoteCode.ofComputable`
  over the decidable comparison fiber.
* `theoremPriceQuoteCode` / `lic_expectations_of_probabilities_closed` — `thm:epr` over the
  constructed `LIA` with **no reflection hypotheses**: the quoted LUV is built from the
  market program and its exactness is the market certificate's `quote_exact`.
-/

namespace LogicalInduction

open Nat.Partrec (Code)
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

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
/-- **`threshold_poly` discharged for the universal quotation schema.**  One poly-fueled
program emits the encoded threshold sentence of `arithmeticThresholdLUV code n` at mesh
threshold `i/k` from the packed query `⟨n,⟨k,i⟩⟩`: runtime `gcdc` reduction of the mesh
rational, an `ifzSel` zero-denominator fallback, and the fixed atom shell around the
selector constant.  This is the obligation every `RationalQuoteCode` carries; it had never
before been discharged.
Paper node: `def:ec`, `thm:epr`, `thm:er` -/
lemma arithmeticThresholdLUV_polyThresholdCodeSeq (code : ℕ) :
    LUV.PolyThresholdCodeSeq (fun n => arithmeticThresholdLUV code n) := by
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
  rw [arithmeticThresholdLUV_gt, encode_quoteAtom]
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
obligation is the Part-A emitter. -/
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
    threshold_poly := arithmeticThresholdLUV_polyThresholdCodeSeq b.code }

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

/-- Exact rational day-`n` expectation of a varying LUV under a certified market: the
rational value whose cast is `(X n).expect P n` (`def:e` computed through the market
program's exact quotes). -/
def MarketComputation.expectQuote {P : History} (market : MarketComputation P)
    (X : ℕ → LUV) (n : ℕ) : ℚ :=
  (∑ i ∈ Finset.range n,
    market.quote n (Encodable.encode ((X n).gt ((i : ℚ) / (n : ℚ))))) / (n : ℚ)

/-- `expectQuote` is exactly the real expectation sequence, through the market
certificate's `quote_exact`. -/
lemma MarketComputation.expectQuote_cast {P : History} (market : MarketComputation P)
    (X : ℕ → LUV) (n : ℕ) :
    (X n).expect P n = (market.expectQuote X n : ℝ) := by
  have hq : ∀ i : ℕ, P n ((X n).gt ((i : ℚ) / (n : ℚ))) =
      ((market.quote n (Encodable.encode ((X n).gt ((i : ℚ) / (n : ℚ)))) : ℚ) : ℝ) :=
    fun i => market.quote_exact n _
  simp only [LUV.expect, LUV.expectApprox, MarketComputation.expectQuote, hq]
  push_cast
  ring

/-- `expectQuote` lands in `[0,1]`: an average of `[0,1]` quotes. -/
lemma MarketComputation.expectQuote_mem_Icc {P : History} (market : MarketComputation P)
    (X : ℕ → LUV) (n : ℕ) :
    0 ≤ market.expectQuote X n ∧ market.expectQuote X n ≤ 1 := by
  unfold MarketComputation.expectQuote
  have hterm : ∀ i ∈ Finset.range n,
      (0 : ℚ) ≤ market.quote n (Encodable.encode ((X n).gt ((i : ℚ) / (n : ℚ)))) ∧
        market.quote n (Encodable.encode ((X n).gt ((i : ℚ) / (n : ℚ)))) ≤ 1 :=
    fun i _ => market.quote_mem_Icc n _
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i hi => (hterm i hi).1) (Nat.cast_nonneg n)
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · rw [div_le_one (by exact_mod_cast hn)]
      calc (∑ i ∈ Finset.range n,
            market.quote n (Encodable.encode ((X n).gt ((i : ℚ) / (n : ℚ)))))
          ≤ ∑ _i ∈ Finset.range n, (1 : ℚ) :=
            Finset.sum_le_sum fun i hi => (hterm i hi).2
        _ = (n : ℚ) := by simp

/-- The natural-cast rational sequence is primitive recursive (closed encode form
`⌜(n:ℚ)⌝ = pair (n+n) 1`). -/
lemma ratNatCast_prim : Primrec fun n : ℕ => (n : ℚ) := by
  refine Primrec.encode_iff.mp ?_
  have h : Primrec fun n : ℕ => Nat.pair (n + n) 1 :=
    Primrec₂.natPair.comp (Primrec.nat_add.comp Primrec.id Primrec.id) (Primrec.const 1)
  exact h.of_eq fun n => by rw [encode_rat_natCast, two_mul]

set_option maxHeartbeats 1000000 in
/-- **`expectQuote` is computable.**  Threshold codes come from the LUV sequence's poly
emitter, each cell quote from the market program, the bounded sum by `Nat.rec`, and the
final average by `ratDiv_prim`. -/
lemma MarketComputation.expectQuote_computable {P : History} (market : MarketComputation P)
    {X : ℕ → LUV} (hX : LUV.PolyThresholdCodeSeq X) :
    Computable (market.expectQuote X) := by
  obtain ⟨cX, hcX⟩ := hX
  -- The threshold-code function of `⟨day, index⟩`.
  have hpack : Computable fun p : ℕ × ℕ => Nat.pair p.1 (Nat.pair p.1 p.2) :=
    Primrec₂.natPair.to_comp.comp Computable.fst
      (Primrec₂.natPair.to_comp.comp Computable.fst Computable.snd)
  have hgt : Computable fun p : ℕ × ℕ =>
      Encodable.encode ((X p.1).gt ((p.2 : ℚ) / (p.1 : ℚ))) :=
    (hcX.primrec.to_comp.comp hpack).of_eq fun p => by simp [Nat.unpair_pair]
  -- The per-cell exact quote.
  have hcell : Computable fun p : ℕ × ℕ =>
      market.quote p.1 (Encodable.encode ((X p.1).gt ((p.2 : ℚ) / (p.1 : ℚ)))) :=
    (market.quote_comp_computable Computable.fst hgt : _)
  -- The bounded sum, by primitive recursion on the day.
  have hstepC : Computable fun q : ℕ × (ℕ × ℚ) =>
      q.2.2 + market.quote q.1
        (Encodable.encode ((X q.1).gt ((q.2.1 : ℚ) / (q.1 : ℚ)))) := by
    -- `( … : _)` ascriptions here and on `hcell` are load-bearing (see Part B note).
    have hc : Computable fun q : ℕ × (ℕ × ℚ) =>
        market.quote q.1
          (Encodable.encode ((X q.1).gt ((q.2.1 : ℚ) / (q.1 : ℚ)))) :=
      (hcell.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)) : _)
    exact (ratAdd_prim.to_comp.comp (Computable.snd.comp Computable.snd) hc : _)
  have hsum : Computable fun n : ℕ => ∑ i ∈ Finset.range n,
      market.quote n (Encodable.encode ((X n).gt ((i : ℚ) / (n : ℚ)))) := by
    have hrec := Computable.nat_rec Computable.id (Computable.const (0 : ℚ)) hstepC.to₂
    refine hrec.of_eq fun n => ?_
    have key : ∀ m : ℕ, (Nat.rec (motive := fun _ => ℚ) 0
        (fun i s => s + market.quote n
          (Encodable.encode ((X n).gt ((i : ℚ) / (n : ℚ))))) m) =
        ∑ i ∈ Finset.range m,
          market.quote n (Encodable.encode ((X n).gt ((i : ℚ) / (n : ℚ)))) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, ← ih]
    exact key n
  -- The final average.
  exact ((ratDiv_prim.to_comp.comp hsum ratNatCast_prim.to_comp : _) :
    Computable (market.expectQuote X))

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
  lic_expectations_of_probabilities_ofCode_unconditional (T := T) φ hφ
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
  lic_iterated_expectations_ofCode_unconditional (T := T) X hX
    (theoremExpectationQuoteCode T X hX)
    ((theoremMarketComputation T).expectQuote_cast X)

end

end

#print axioms arithmeticThresholdLUV_polyThresholdCodeSeq
#print axioms RationalQuoteCode.ofComputable
#print axioms lic_expectations_of_probabilities_closed
#print axioms MarketComputation.expectQuote_computable
#print axioms lic_iterated_expectations_closed

end LogicalInduction
