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

/-- The exact rational quote of a certified market program along any computable
sentence-code stream is a total computable rational sequence. -/
lemma MarketComputation.quote_comp_computable {P : History} (market : MarketComputation P)
    {g : ℕ → ℕ} (hg : Computable g) :
    Computable fun n => market.quote n (g n) := by
  have hin : Computable fun n => Nat.pair n (g n) :=
    Primrec₂.natPair.to_comp.comp Computable.id hg
  have heval : Partrec fun n => market.code.eval (Nat.pair n (g n)) :=
    Nat.Partrec.Code.eval_part.comp (Computable.const market.code) hin
  have henc : Computable fun n => Encodable.encode (market.quote n (g n)) :=
    heval.of_eq fun n => Part.eq_some_iff.mpr
      (by simpa [Nat.unpair_pair] using market.code_spec (Nat.pair n (g n)))
  have hdec : Computable fun n =>
      (Encodable.decode (α := ℚ) (Encodable.encode (market.quote n (g n)))).getD 0 :=
    Computable.option_getD (Computable.decode.comp henc) (Computable.const 0)
  exact hdec.of_eq fun n => by simp

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
    ((theoremMarketComputation T).quote_comp_computable hφ.choose_spec.primrec.to_comp)
    (fun n => by
      have h := (theoremMarketComputation T).price_mem_Icc n (φ n)
      rw [(theoremMarketComputation T).quote_exact n (φ n)] at h
      exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩)

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

end

end

#print axioms arithmeticThresholdLUV_polyThresholdCodeSeq
#print axioms RationalQuoteCode.ofComputable
#print axioms lic_expectations_of_probabilities_closed

end LogicalInduction
