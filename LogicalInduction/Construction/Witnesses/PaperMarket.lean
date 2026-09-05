import LogicalInduction.Construction.Witnesses.PaperTheoryDP

/-!
# The single paper-facing market and its endpoints

The paper fixes one deductive process and prices everything against the one market its
construction builds over it.  `paperDP` (`PaperTheoryDP.lean`) is that process — the
computation/quotation literal stream together with the `Θ`-complete first-order theorem
stream — and this file is where the self-reference family is stated over it.

Three things make the transfer mechanical, and all three are proved upstream:

* `paperQuotationPresentation` is the monotone lift of `quotationPresentation` along
  `theoremDP.D k ⊆ paperDP.D k`.  Every field of `QuotationTheoryPresentation` is either
  theory-side or an "enters some stage" claim, so a larger process satisfies it as soon as
  the smaller one does; only the stage program is supplied afresh.
* `paperDP_hworld` is the stage-indexed market non-vacuity, from consistency of `T` via
  satisfiability — no Σ₁-soundness anywhere.
* `paperMarketComputation` is the `LIA`'s own exact market program over `paperDP`, an
  instance of the process-generic `liaMarketComputation`.

The family priced here is `thm:epr` (tex:2014), `thm:er` (tex:2022), `thm:ref` (tex:1969),
`thm:cee` (tex:2045), `thm:ceu` (tex:2056), `thm:ccee` (tex:2068), `thm:st` (tex:2092) and
`thm:lp` (tex:1992), all in the one market `liaHistory (paperDP T)`.

Nothing here is a new theorem about the market: each endpoint is the generic `_ofCode` /
`_ofRepresentation` / `_ofDiagonal` statement instantiated at those three, and each
`_closed` form additionally constructs the quote object out of the market program itself,
so the only hypotheses left are the caller's sequence and its `def:ec` write-out codes.  The
market's own quote codes are `paperDiagonalQuoteCode`, `paperPriceQuoteCode`,
`paperExpectationQuoteCode`, `paperFutureQuoteCode`, `paperDeferredExpectationQuoteCode`,
`paperConfidenceQuoteCode`, `paperIntervalQuoteCode`, `paperDeferredWeightQuoteCode` and
`paperConditionalExpectationQuoteCode`.

Which certificate class each lane asks for: write-out `BigSentenceCodes` / `DigitRatCodes` on
the sentence and tolerance lanes, `LUV.RpnThresholdCodeSeq` on the LUV threshold lane, and
`LUV.BigThresholdCodeSeq` on `thm:st` — see the README's rendering-sensitivity note.  What
`thm:ref` and `thm:st` ask of their bounds is `def:ece` ℙ-generability rather than efficient
writability: computability is recovered from the feature presentation by
`PGenerableRat.computable`, and nothing spells the bound out under a clock because the
quoted sentence is a code-indexed atom (`dd:quote-code`); see `notes/paper-errata.md` PE6.

`thm:ccee` carries a disclosed type-`(c)` substitution: the left quoted product is realized
on a finite mesh to within `1/(n+1)` rather than exactly (`dd:mesh`).  The conclusion's form
is unchanged, and `indicatorProductLUV_exact_left_reflected` inhabits the relaxed certificate
at zero slack.

The one canonical endpoint *not* priced here is `thm:ccee`'s generalized semantic-extension
form `lic_no_expected_net_update_conditional_exact_canonical`, which keeps the
semantic-lifted `canonicalCCEEDP` as its own construction by ruling
(`SemanticLiftedCCEE.lean`), because that fixed enlarged language is what buys exact semantic
multiplication for an arbitrary threshold-only source.  The paper rendering of `thm:ccee` at
zero slack, `lic_no_expected_net_update_conditional_paperLUV_closed`
(`PaperExactCCEE.lean`), is priced on `liaHistory (paperDP T)` like the rest, as is the
`thm:ccee` closed form at the disclosed `1/(n+1)` slack stated here.

`thm:lp` sits outside the `𝗣𝗔⁻` section because `𝗜𝚺₁ ⪯ T` implies `𝗣𝗔⁻ ⪯ T` by instance, and
carrying both would leave a redundant pair in the elaborated signature; `omit` cannot do
this, because instance search reaches a section variable that is in the local context whether
or not the declaration lists it.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional
open Filter Topology

variable (T : ArithmeticTheory)

/-! ## The generic endpoints over the single market -/

section PeanoMinus
variable [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- The canonical public diagonal quote for the single market at threshold `p`.
Paper node: `thm:lp` -/
noncomputable def paperDiagonalQuoteCode (p : ℚ) :
    ParameterizedDiagonalQuoteCode T
      (diagonalPriceTruth (paperMarketComputation T) p) :=
  parameterizedDiagonalQuoteCodeOfMarket (paperMarketComputation T) T p

/-- `thm:epr`, unconditional over `LIA`.
Paper node: `thm:epr` -/
theorem lic_expectations_of_probabilities_ofCode_unconditional
    {value : ℕ → ℚ} (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
    (q : RationalQuoteCode T value)
    (hexact : ∀ n, liaHistory (paperDP T) n (φ n) = (value n : ℝ)) :
    (fun n => liaHistory (paperDP T) n (φ n)) ≈ₙ
      fun n => (q.luv n).expect (liaHistory (paperDP T)) n :=
  haveI := paperLIA T
  lic_expectations_of_probabilities_ofCode (paperQuotationPresentation T)
    (liaHistory (paperDP T)) φ hφ q hexact
    (paperDP_hworld T)

/-- `thm:er`, unconditional over `LIA`.
Paper node: `thm:er` -/
theorem lic_iterated_expectations_ofCode_unconditional
    {value : ℕ → ℚ} (X : ℕ → LUV) (hX : LUV.RpnThresholdCodeSeq X)
    (q : RationalQuoteCode T value)
    (hexact : ∀ n, (X n).expect (liaHistory (paperDP T)) n = (value n : ℝ)) :
    (fun n => (X n).expect (liaHistory (paperDP T)) n) ≈ₙ
      fun n => (q.luv n).expect (liaHistory (paperDP T)) n :=
  haveI := paperLIA T
  lic_iterated_expectations_ofCode (paperQuotationPresentation T)
    (liaHistory (paperDP T)) X hX q hexact
    (paperDP_hworld T)

/-- `thm:ref` (introspection), unconditional over `LIA`.
Paper node: `thm:ref` -/
theorem lic_introspection_ofCode_unconditional
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ) (a b δ : ℕ → ℚ)
    (lowerFeature : ℕ → EF)
    (hlower : GeneratedRatFeature (liaHistory (paperDP T)) a lowerFeature)
    (upperFeature : ℕ → EF)
    (hupper : GeneratedRatFeature (liaHistory (paperDP T)) b upperFeature)
    (hδ : DigitRatCodes δ)
    (hδpos : ∀ n, 0 < δ n)
    (hδzero : Tendsto (fun n ↦ (δ n : ℝ)) atTop (𝓝 0))
    (hab : ∀ n, 0 ≤ a n ∧ a n ≤ 1 ∧ 0 ≤ b n ∧ b n ≤ 1)
    (q : BooleanQuoteCode T (fun n ↦
      (a n : ℝ) < liaHistory (paperDP T) n (φ n) ∧
        liaHistory (paperDP T) n (φ n) < (b n : ℝ))) :
    ∃ ε : ℕ → ℚ, (∀ n, 0 < ε n) ∧ Tendsto (fun n ↦ (ε n : ℝ)) atTop (𝓝 0) ∧
      ∀ n,
        (((a n : ℝ) + δ n < liaHistory (paperDP T) n (φ n) ∧
            liaHistory (paperDP T) n (φ n) < (b n : ℝ) - δ n) →
          1 - (ε n : ℝ) < liaHistory (paperDP T) n (q.sentence n)) ∧
        ((¬ ((a n : ℝ) - δ n < liaHistory (paperDP T) n (φ n) ∧
              liaHistory (paperDP T) n (φ n) < (b n : ℝ) + δ n)) →
          liaHistory (paperDP T) n (q.sentence n) < (ε n : ℝ)) :=
  haveI := paperLIA T
  lic_introspection_ofCode (paperQuotationPresentation T) (liaHistory (paperDP T))
    φ hφ a b δ lowerFeature hlower upperFeature hupper hδ hδpos hδzero hab q
    (paperDP_hworld T)

/-- `thm:cee` (expected future expectations), unconditional over `LIA`.
Paper node: `thm:cee` -/
theorem lic_expected_future_expectations_ofRepresentation_unconditional
    (f : DeferralFunction)
    (X Y : ℕ → LUV) (hX : LUV.RpnThresholdCodeSeq X) (hY : LUV.RpnThresholdCodeSeq Y)
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      ∃ x, v.ValuesAt (X n) x)
    (reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      v.ValuesAt (Y n) ((X n).expect (liaHistory (paperDP T)) (f n))) :
    (fun n ↦ (X n).expect (liaHistory (paperDP T)) n) ≈ₙ
      fun n ↦ (Y n).expect (liaHistory (paperDP T)) n :=
  haveI := paperLIA T
  lic_expected_future_expectations_ofRepresentation (P := liaHistory (paperDP T))
    (DP := paperDP T) f X Y hX hY source_valued reflected
    (paperDP_hworld T)

/-- `thm:ceu` (no expected net update), unconditional over `LIA`.
Paper node: `thm:ceu` -/
theorem lic_no_expected_net_update_ofRepresentation_unconditional
    (f : DeferralFunction)
    (φ : ℕ → Sentence) (Y : ℕ → LUV)
    (hφ : BigSentenceCodes φ) (hY : LUV.RpnThresholdCodeSeq Y)
    (reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      v.ValuesAt (Y n) (liaHistory (paperDP T) (f n) (φ n))) :
    (fun n ↦ liaHistory (paperDP T) n (φ n)) ≈ₙ
      fun n ↦ (Y n).expect (liaHistory (paperDP T)) n :=
  haveI := paperLIA T
  lic_no_expected_net_update_ofRepresentation (P := liaHistory (paperDP T))
    (DP := paperDP T) f φ Y hφ hY reflected
    (paperDP_hworld T)

/-- `thm:ccee` (conditional no expected net update), unconditional over `LIA`.
Paper node: `thm:ccee` -/
theorem lic_no_expected_net_update_conditional_ofRepresentation_unconditional
    (f : DeferralFunction)
    (X Z Z' : ℕ → LUV) (w : ℕ → ℚ)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat (liaHistory (paperDP T)) w)
    (hX : LUV.RpnThresholdCodeSeq X) (hZ : LUV.RpnThresholdCodeSeq Z)
    (hZ' : LUV.RpnThresholdCodeSeq Z')
    (slack : ℕ → ℝ) (slack_tendsto : Tendsto slack atTop (𝓝 0))
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      ∃ x, v.ValuesAt (X n) x)
    (left_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      ∀ x, v.ValuesAt (X n) x →
        ∃ z, v.ValuesAt (Z n) z ∧ |z - x * w (f n)| ≤ slack n)
    (right_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      v.ValuesAt (Z' n) ((X n).expect (liaHistory (paperDP T)) (f n) * w (f n))) :
    (fun n ↦ (Z n).expect (liaHistory (paperDP T)) n) ≈ₙ
      fun n ↦ (Z' n).expect (liaHistory (paperDP T)) n :=
  haveI := paperLIA T
  lic_no_expected_net_update_conditional_ofRepresentation (P := liaHistory (paperDP T))
    (DP := paperDP T) f X Z Z' w weight_mem weight_generable hX hZ hZ'
    slack slack_tendsto source_valued left_reflected right_reflected
    (paperDP_hworld T)

/-- `thm:st` (self-trust), unconditional over `LIA`.  The confidence threshold `p` is
P-generable (`def:ece`) against the constructed market, presented by its feature
expression.
Paper node: `thm:st` -/
theorem lic_self_trust_ofRepresentation_unconditional
    (f : DeferralFunction)
    (φ : ℕ → Sentence) (δ p : ℕ → ℚ) (A B : ℕ → LUV)
    (delta_pos : ∀ n, 0 < δ n) (probability_mem : ∀ n, 0 ≤ p n ∧ p n ≤ 1)
    (hφ : BigSentenceCodes φ) (hδ : DigitRatCodes δ)
    (pFeature : ℕ → EF)
    (hp : GeneratedRatFeature (liaHistory (paperDP T)) p pFeature)
    (hA : LUV.BigThresholdCodeSeq A) (hB : LUV.BigThresholdCodeSeq B)
    (confidence_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      v.ValuesAt (B n) (ctsInd (δ n) (liaHistory (paperDP T) (f n) (φ n)) (p n)))
    (product_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      v.ValuesAt (A n)
        (v.payout (φ n) * ctsInd (δ n) (liaHistory (paperDP T) (f n) (φ n)) (p n))) :
    (fun n ↦ (A n).expect (liaHistory (paperDP T)) n) ≳ₙ
      fun n ↦ (p n : ℝ) * (B n).expect (liaHistory (paperDP T)) n :=
  haveI := paperLIA T
  lic_self_trust_ofRepresentation (P := liaHistory (paperDP T)) (DP := paperDP T)
    f φ δ p A B delta_pos probability_mem hφ hδ pFeature hp hA hB
    confidence_reflected product_reflected
    (paperDP_hworld T)

/-! ## The market's own quote codes, and the closed-form endpoints they discharge -/

/-- The canonical quote code of the constructed `LIA` market's own prices along a
write-out codeable sentence sequence (`def:ec`).  No caller-supplied semantic relation: the value
program is the market program, and range comes from its certificate.
Paper node: `thm:epr` -/
noncomputable def paperPriceQuoteCode (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ) :
    RationalQuoteCode T (fun n =>
      (paperMarketComputation T).quote n (Encodable.encode (φ n))) :=
  RationalQuoteCode.ofComputable T
    ((paperMarketComputation T).quote_comp_computable Computable.id
      hφ.primrec.to_comp)
    (fun n => (paperMarketComputation T).quote_mem_Icc n (φ n))

/-- **`thm:epr`, closed form over the constructed `LIA`** — no reflection hypotheses.
For every efficiently codeable sentence sequence, the market's price agrees asymptotically
with its own expectation of the *constructed* quoted-price LUV.  The quote object is
`paperPriceQuoteCode`; its exactness is the market certificate's `quote_exact`, so the
only remaining hypotheses are the sequence and its `def:ec` write-out codes.
Paper node: `thm:epr` -/
theorem lic_expectations_of_probabilities_closed
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ) :
    (fun n => liaHistory (paperDP T) n (φ n)) ≈ₙ
      fun n => ((paperPriceQuoteCode T φ hφ).luv n).expect (liaHistory (paperDP T)) n :=
  lic_expectations_of_probabilities_ofCode_unconditional (T := T) φ hφ
    (paperPriceQuoteCode T φ hφ)
    (fun n => (paperMarketComputation T).quote_exact n (φ n))

/-- The canonical quote code of the constructed `LIA` market's own day-`n` expectations of
an efficiently codeable LUV sequence.  The value program is the expectation compiler over
the market program; range and exactness come from its certificate.
Paper node: `thm:er` -/
noncomputable def paperExpectationQuoteCode (X : ℕ → LUV)
    (hX : LUV.RpnThresholdCodeSeq X) :
    RationalQuoteCode T ((paperMarketComputation T).expectQuote X) :=
  RationalQuoteCode.ofComputable T
    ((paperMarketComputation T).expectQuote_computable hX)
    ((paperMarketComputation T).expectQuote_mem_Icc X)

/-- The future-quote code: `value n = quote (f n) ⌜φ n⌝`, the market's own deferred-day
price of the day-`n` sentence.  No caller-supplied semantic relation.
Paper node: `thm:ceu` -/
noncomputable def paperFutureQuoteCode (f : DeferralFunction)
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ) :
    RationalQuoteCode T (fun n =>
      (paperMarketComputation T).quote (f.f n) (Encodable.encode (φ n))) :=
  RationalQuoteCode.ofComputable T
    ((paperMarketComputation T).quote_comp_computable f.computable
      hφ.primrec.to_comp)
    (fun n => (paperMarketComputation T).quote_mem_Icc (f.f n) (φ n))

/-- **`thm:ceu` (no expected net update), closed form over the constructed `LIA`** — no
reflection hypotheses.  The quoted future-price LUV is constructed from the market
program itself; only the sentence sequence, its `def:ec` write-out codes, and the
deferral function remain.
Paper node: `thm:ceu` -/
theorem lic_no_expected_net_update_closed
    (f : DeferralFunction)
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ) :
    (fun n ↦ liaHistory (paperDP T) n (φ n)) ≈ₙ
      fun n ↦ ((paperFutureQuoteCode T f φ hφ).luv n).expect
        (liaHistory (paperDP T)) n :=
  lic_no_expected_net_update_ofRepresentation_unconditional (T := T) f φ
    ((paperFutureQuoteCode T f φ hφ).luv)
    hφ
    (paperFutureQuoteCode T f φ hφ).poly
    (fun n v hv => by
      have h := RationalQuoteCode.reflected (paperQuotationPresentation T)
        (paperFutureQuoteCode T f φ hφ) n v hv
      rwa [← (paperMarketComputation T).quote_exact (f.f n) (φ n)] at h)

/-- The deferred-expectation quote code: `value n = expectQuoteAt X n (f n)`, the
market's own day-`f n` expectation of the day-`n` LUV.
Paper node: `thm:cee` -/
noncomputable def paperDeferredExpectationQuoteCode (f : DeferralFunction)
    (X : ℕ → LUV) (hX : LUV.RpnThresholdCodeSeq X) :
    RationalQuoteCode T (fun n =>
      (paperMarketComputation T).expectQuoteAt X n (f.f n)) :=
  -- The `( … : _)` ascription is load-bearing: it forces the expected type before
  -- `Computable.comp` unifies (see `decodedQuotationRat_lt_computablePred` in
  -- `QuoteCodeOfMarket.lean` for the same point stated in full).
  have hcomp : Computable fun n =>
      (paperMarketComputation T).expectQuoteAt X n (f.f n) :=
    (((paperMarketComputation T).expectQuoteAt_computable hX).comp
      (Computable.id.pair f.computable) : _)
  RationalQuoteCode.ofComputable T hcomp
    (fun n => (paperMarketComputation T).expectQuoteAt_mem_Icc X n (f.f n))

/-- **`thm:cee` (expected future expectations), closed form over the constructed `LIA`**
— the reflection data is constructed from the market program; only the source LUV
sequence, its `def:ec` token-metered threshold codes, its own theory-valuedness
(`source_valued`, the paper's premise that `X` is a genuine LUV of the theory), and the
deferral function remain.
Paper node: `thm:cee` -/
theorem lic_expected_future_expectations_closed
    (f : DeferralFunction)
    (X : ℕ → LUV) (hX : LUV.RpnThresholdCodeSeq X)
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      ∃ x, v.ValuesAt (X n) x) :
    (fun n ↦ (X n).expect (liaHistory (paperDP T)) n) ≈ₙ
      fun n ↦ ((paperDeferredExpectationQuoteCode T f X hX).luv n).expect
        (liaHistory (paperDP T)) n :=
  lic_expected_future_expectations_ofRepresentation_unconditional (T := T) f X
    ((paperDeferredExpectationQuoteCode T f X hX).luv)
    hX
    (paperDeferredExpectationQuoteCode T f X hX).poly source_valued
    (fun n v hv => by
      have h := RationalQuoteCode.reflected (paperQuotationPresentation T)
        (paperDeferredExpectationQuoteCode T f X hX) n v hv
      rwa [← (paperMarketComputation T).expectQuoteAt_cast X n (f.f n)] at h)

/-- **`thm:er`, closed form over the constructed `LIA`** — no reflection hypotheses.
For every efficiently codeable LUV sequence, the market's expectation agrees
asymptotically with its expectation of the *constructed* quoted-expectation LUV.  Only
the LUV sequence and its `def:ec` token-metered threshold codes remain.
Paper node: `thm:er` -/
theorem lic_iterated_expectations_closed
    (X : ℕ → LUV) (hX : LUV.RpnThresholdCodeSeq X) :
    (fun n => (X n).expect (liaHistory (paperDP T)) n) ≈ₙ
      fun n => ((paperExpectationQuoteCode T X hX).luv n).expect
        (liaHistory (paperDP T)) n :=
  lic_iterated_expectations_ofCode_unconditional (T := T) X hX
    (paperExpectationQuoteCode T X hX)
    ((paperMarketComputation T).expectQuote_cast X)

/-- The confidence quote code for `thm:st`: the market's own continuous indicator of its
deferred-day price against the target probability,
`value n = ratCtsInd (δ n) (quote (f n) ⌜φ n⌝) (p n)`.

The threshold `p` is P-generable (`def:ece`), exactly as in the paper: the emitter recovers
a program for `p` from the feature presentation by parsing the emitted serialization
(`BigSpliceStream.feature_primrec`) and evaluating it against this market
(`PGenerableRat.computable`).

What the quote code needs of the tolerance `δ` is *computability*, not efficiency: the
quoted value is a code-indexed atom, so nothing here spells `δ n` out under a polynomial
clock.  The hypothesis is therefore `Computable δ`, which `DigitRatCodes.computable`
supplies at the call sites that do carry the efficiency certificate for other reasons.
This is the same narrowing the sibling `thm:ref` code (`paperIntervalQuoteCode`) makes.
Paper node: `thm:st` -/
noncomputable def paperConfidenceQuoteCode (f : DeferralFunction)
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ) (δ p : ℕ → ℚ)
    (hδ : Computable δ) (hp : PGenerableRat (liaHistory (paperDP T)) p) :
    RationalQuoteCode T (fun n => ratCtsInd (δ n)
      ((paperMarketComputation T).quote (f n) (Encodable.encode (φ n))) (p n)) :=
  have hquote : Computable fun n =>
      (paperMarketComputation T).quote (f n) (Encodable.encode (φ n)) :=
    ((paperMarketComputation T).quote_comp_computable f.computable
      hφ.primrec.to_comp : _)
  have hval : Computable fun n => ratCtsInd (δ n)
      ((paperMarketComputation T).quote (f n) (Encodable.encode (φ n))) (p n) :=
    (ratCtsInd_computable.comp (hδ.pair
      (hquote.pair (hp.computable (paperMarketComputation T)))) : _)
  RationalQuoteCode.ofComputable T hval (fun _ => ratCtsInd_mem_Icc _ _ _)

/-- Cast identity for the confidence value against the real market. -/
lemma paperConfidence_value_cast (f : DeferralFunction) (φ : ℕ → Sentence)
    (δ p : ℕ → ℚ) (n : ℕ) :
    ctsInd (δ n) (liaHistory (paperDP T) (f n) (φ n)) ((p n : ℝ)) =
      ((ratCtsInd (δ n) ((paperMarketComputation T).quote (f n)
        (Encodable.encode (φ n))) (p n) : ℚ) : ℝ) := by
  rw [(paperMarketComputation T).quote_exact (f n) (φ n), ratCtsInd_cast]

set_option maxHeartbeats 1000000 in
/-- The interval quote code for `thm:ref`: one Boolean decider names the fact
`a n < Pₙ(φ n) < b n`, computed from the market program's exact rational quote.  This is
the introspection target sentence, constructed with no caller-supplied truth relation.

**The bounds are only ℙ-generable** (`def:ece`), exactly as the paper states them.  What the
decider needs of `a` and `b` is *computability*, not efficiency, and computability is
recovered from the feature presentation itself: `PGenerableRat.computable` dovetails the
feature's evaluation against the market's own quote program.  This is the same route
`paperConfidenceQuoteCode` takes for `thm:st`.  Nothing here asks for an efficiently
writable numeral, because the quoted sentence is a *code-indexed atom* (`dd:quote-code`)
rather than a formula spelling `a n` and `b n` out — see the `thm:ref` entry of
`notes/paper-errata.md` for why the paper's own proof does need the stronger property.
Paper node: `thm:ref` -/
noncomputable def paperIntervalQuoteCode (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
    (a b : ℕ → ℚ)
    (lowerFeature : ℕ → EF)
    (hlower : GeneratedRatFeature (liaHistory (paperDP T)) a lowerFeature)
    (upperFeature : ℕ → EF)
    (hupper : GeneratedRatFeature (liaHistory (paperDP T)) b upperFeature) :
    BooleanQuoteCode T (fun n ↦
      (a n : ℝ) < liaHistory (paperDP T) n (φ n) ∧
        liaHistory (paperDP T) n (φ n) < (b n : ℝ)) := by
  have ha : Computable a :=
    PGenerableRat.computable (paperMarketComputation T) ⟨lowerFeature, hlower⟩
  have hb : Computable b :=
    PGenerableRat.computable (paperMarketComputation T) ⟨upperFeature, hupper⟩
  refine BooleanQuoteCode.ofComputable ?_
  rw [ComputablePred.computable_iff]
  refine ⟨fun n =>
    (!(decide ((paperMarketComputation T).quote n (Encodable.encode (φ n)) ≤ a n))) &&
      (!(decide (b n ≤ (paperMarketComputation T).quote n (Encodable.encode (φ n))))),
    ?_, ?_⟩
  · have hq : Computable fun n =>
        (paperMarketComputation T).quote n (Encodable.encode (φ n)) :=
      ((paperMarketComputation T).quote_comp_computable Computable.id
        hφ.primrec.to_comp : _)
    have hleB : Primrec fun z : ℚ × ℚ => decide (z.1 ≤ z.2) := ratLE_prim.decide
    have h1 : Computable fun n => decide
        ((paperMarketComputation T).quote n (Encodable.encode (φ n)) ≤ a n) :=
      (hleB.to_comp.comp (hq.pair ha) : _)
    have h2 : Computable fun n => decide
        (b n ≤ (paperMarketComputation T).quote n (Encodable.encode (φ n))) :=
      (hleB.to_comp.comp (hb.pair hq) : _)
    have hn1 := (Primrec.dom_bool Bool.not).to_comp.comp h1
    have hn2 := (Primrec.dom_bool Bool.not).to_comp.comp h2
    exact ((Primrec.dom_bool₂ Bool.and).to_comp.comp hn1 hn2 : _)
  · funext n
    rw [(paperMarketComputation T).quote_exact n (φ n)]
    simp only [Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, not_le, Rat.cast_lt]

/-- **`thm:ref` (introspection), closed form over the constructed `LIA`** — the interval
quote is constructed from the market program; the remaining hypotheses are exactly the
paper's own — the interval bounds' market-generated feature presentations (`def:ece`
ℙ-generability, *not* efficient writability), the vanishing width, and the range side
conditions.  See `notes/paper-errata.md` PE6 for why the paper's own proof needs more than
it states, and why this route does not.
Paper node: `thm:ref` -/
theorem lic_introspection_closed
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ) (a b δ : ℕ → ℚ)
    (lowerFeature : ℕ → EF)
    (hlower : GeneratedRatFeature (liaHistory (paperDP T)) a lowerFeature)
    (upperFeature : ℕ → EF)
    (hupper : GeneratedRatFeature (liaHistory (paperDP T)) b upperFeature)
    (hδ : DigitRatCodes δ)
    (hδpos : ∀ n, 0 < δ n)
    (hδzero : Tendsto (fun n ↦ (δ n : ℝ)) atTop (𝓝 0))
    (hab : ∀ n, 0 ≤ a n ∧ a n ≤ 1 ∧ 0 ≤ b n ∧ b n ≤ 1) :
    ∃ ε : ℕ → ℚ, (∀ n, 0 < ε n) ∧ Tendsto (fun n ↦ (ε n : ℝ)) atTop (𝓝 0) ∧
      ∀ n,
        (((a n : ℝ) + δ n < liaHistory (paperDP T) n (φ n) ∧
            liaHistory (paperDP T) n (φ n) < (b n : ℝ) - δ n) →
          1 - (ε n : ℝ) < liaHistory (paperDP T) n
            ((paperIntervalQuoteCode T φ hφ a b lowerFeature hlower
              upperFeature hupper).sentence n)) ∧
        ((¬ ((a n : ℝ) - δ n < liaHistory (paperDP T) n (φ n) ∧
              liaHistory (paperDP T) n (φ n) < (b n : ℝ) + δ n)) →
          liaHistory (paperDP T) n
            ((paperIntervalQuoteCode T φ hφ a b lowerFeature hlower
              upperFeature hupper).sentence n) < (ε n : ℝ)) :=
  lic_introspection_ofCode_unconditional (T := T) φ
    hφ a b δ lowerFeature hlower
    upperFeature hupper hδ hδpos hδzero hab
    (paperIntervalQuoteCode T φ hφ a b lowerFeature hlower upperFeature hupper)

/-- **`thm:st` (self-trust), closed form over the constructed `LIA`** — no reflection
hypotheses.  Both quoted LUVs are constructed: `B` is the confidence quote code of the
market's own deferred-day price, and `A` is its indicator product with `φ n`.  Only the
sentence sequence with its `def:ec` write-out codes, the deferral function, and the
threshold data remain.  The two threshold obligations this discharges internally are at
the same write-out meter (`LUV.BigThresholdCodeSeq`): `A`'s comes from
`indicatorProductLUV_bigThresholdCodeSeq`, whose `⋏`-shell is one emitted token, and `B`'s
is the quote's own threshold stream weakened into the write-out class.  Nothing on this
lane opens a threshold certificate as value-bounded emission data.

The threshold `p` is P-generable (`def:ece`), matching the paper: the quote code recovers
a program for `p` from the feature presentation itself (`PGenerableRat.computable`).  An
e.c. rational sequence is the constant-feature special case — supply
`PGenerableRat.ofDigitRatCodes hp _` for `hp : DigitRatCodes p`, the paper's own
write-out class (`PGenerableRat.ofPolyRatCodes` is the value-bounded corollary).

The tolerance sequence `δ` carries exactly the paper's hypotheses: efficiently codeable
and positive.  Efficient codeability of the reciprocal `1/δ` is *derived* from those two
(`PolyRatCodes.inv_of_pos`), not assumed.
Paper node: `thm:st` -/
theorem lic_self_trust_closed
    (f : DeferralFunction)
    (φ : ℕ → Sentence) (δ p : ℕ → ℚ)
    (delta_pos : ∀ n, 0 < δ n) (probability_mem : ∀ n, 0 ≤ p n ∧ p n ≤ 1)
    (hφ : BigSentenceCodes φ) (hδ : DigitRatCodes δ)
    (hp : PGenerableRat (liaHistory (paperDP T)) p) :
    (fun n ↦ (indicatorProductLUV
          (paperConfidenceQuoteCode T f φ hφ δ p
              hδ.computable hp) φ n).expect
        (liaHistory (paperDP T)) n) ≳ₙ
      fun n ↦ (p n : ℝ) *
        ((paperConfidenceQuoteCode T f φ hφ δ p
            hδ.computable hp).luv n).expect
          (liaHistory (paperDP T)) n := by
  refine lic_self_trust_ofRepresentation_unconditional (T := T) f φ δ p
    (fun n => indicatorProductLUV
      (paperConfidenceQuoteCode T f φ hφ δ p
          hδ.computable hp) φ n)
    (paperConfidenceQuoteCode T f φ hφ δ p
        hδ.computable hp).luv
    delta_pos probability_mem hφ hδ
    hp.choose hp.choose_spec
    (indicatorProductLUV_bigThresholdCodeSeq _ hφ)
    (paperConfidenceQuoteCode T f φ hφ δ p
        hδ.computable hp).poly.toBig
    (fun n v hv => ?_) (fun n v hv => ?_)
  · have h := RationalQuoteCode.reflected (paperQuotationPresentation T)
      (paperConfidenceQuoteCode T f φ hφ δ p
          hδ.computable hp) n v hv
    rwa [← paperConfidence_value_cast T f φ δ p n] at h
  · have h := indicatorProductLUV_valuesAt (paperQuotationPresentation T)
      (paperConfidenceQuoteCode T f φ hφ δ p
          hδ.computable hp) φ n v hv
    rwa [← paperConfidence_value_cast T f φ δ p n] at h

/-! ## `thm:ccee`, closed form at the disclosed mesh slack -/

/-- The deferred-weight quote at the single market.
Paper node: `thm:ccee` -/
noncomputable def paperDeferredWeightQuoteCode (f : DeferralFunction) (w : ℕ → ℚ)
    (hw : PGenerableRat (liaHistory (paperDP T)) w)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) :
    RationalQuoteCode T (fun n => w (f n)) :=
  deferredWeightQuoteCode T (paperMarketComputation T) f w hw weight_mem

/-- The deferred weighted-expectation quote at the single market.
Paper node: `thm:ccee` -/
noncomputable def paperConditionalExpectationQuoteCode (f : DeferralFunction)
    (X : ℕ → LUV) (hX : LUV.RpnThresholdCodeSeq X) (w : ℕ → ℚ)
    (hw : PGenerableRat (liaHistory (paperDP T)) w)
    (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) :
    RationalQuoteCode T (fun n =>
      (paperMarketComputation T).expectQuoteAt X n (f.f n) * w (f.f n)) :=
  conditionalExpectationQuoteCode T (paperMarketComputation T) f X hX w hw weight_mem

/-- **`thm:ccee` (no expected net update under conditionals), closed form over the
constructed `LIA`** — for an **arbitrary** e.c. source family `X`, as the paper states it,
with both quoted products constructed.  `Z` is the mesh product of `X` with the
deferred-weight quote code, and `Z'` the quote of the market's own deferred weighted
expectation.  The remaining hypotheses are the paper's own: the source family with its
`def:ec` token-metered threshold codes and completed-world values (`lem:conluvapprox`,
as in `thm:cee`), the
`[0,1]` P-generable weight, and the deferral function.

**Disclosed type-`(c)`:** the left quoted product is realized to within `1/(n+1)`, not
exactly.  The substitution is `dd:mesh` in the glossary, its construction is the mesh
product in `Construction/Witnesses/QuoteCodeOfMarket.lean`, and the slack is carried by
`ConditionalExpectationQuote.slack`.  The conclusion is an `≈ₙ` between the two market
expectations, exactly as printed; what carries the slack is the certificate that `Z` *is*
the product.
Paper node: `thm:ccee` -/
theorem lic_no_expected_net_update_conditional_closed
    (f : DeferralFunction)
    (X : ℕ → LUV) (hX : LUV.RpnThresholdCodeSeq X)
    (source_valued : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) →
      ∃ x, v.ValuesAt (X n) x)
    (w : ℕ → ℚ) (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat (liaHistory (paperDP T)) w) :
    (fun n ↦ (meshProductLUV
        (paperDeferredWeightQuoteCode T f w weight_generable weight_mem) X n).expect
          (liaHistory (paperDP T)) n) ≈ₙ
      fun n ↦ ((paperConditionalExpectationQuoteCode T f X hX w weight_generable
        weight_mem).luv n).expect (liaHistory (paperDP T)) n := by
  refine lic_no_expected_net_update_conditional_ofRepresentation_unconditional (T := T)
    f X
    (fun n => meshProductLUV
      (paperDeferredWeightQuoteCode T f w weight_generable weight_mem) X n)
    ((paperConditionalExpectationQuoteCode T f X hX w weight_generable weight_mem).luv)
    w weight_mem weight_generable hX
    (meshProductLUV_rpnThresholdCodeSeq _ hX)
    (paperConditionalExpectationQuoteCode T f X hX w weight_generable weight_mem).poly
    (fun n => 1 / ((n : ℝ) + 1)) tendsto_one_div_add_atTop_nhds_zero_nat
    source_valued
    (fun n v hv x hx => meshProductLUV_valuesAt (paperQuotationPresentation T)
      (paperDeferredWeightQuoteCode T f w weight_generable weight_mem) X n v hv hx)
    (fun n v hv => ?_)
  have h := RationalQuoteCode.reflected (paperQuotationPresentation T)
    (paperConditionalExpectationQuoteCode T f X hX w weight_generable weight_mem) n v hv
  rwa [Rat.cast_mul,
    ← (paperMarketComputation T).expectQuoteAt_cast X n (f.f n)] at h

/-! ## Inhabiting the mesh certificate at zero slack

The slack certificate is inhabited at both ends: by the mesh product above for an arbitrary
source, and by the indicator product below at `slack = 0`, which is the exact condition the
certificate generalizes. -/

/-- **N±.** The indicator-source product inhabits the `thm:ccee` certificate at zero slack,
so the slack field is a genuine weakening of an inhabited condition rather than a
replacement of it.
Paper node: `thm:ccee` -/
lemma indicatorProductLUV_exact_left_reflected
    (f : DeferralFunction) (φ : ℕ → Sentence)
    (X : ℕ → LUV) (hind : ∀ n, (X n).IsIndicator (φ n) (paperDP T))
    (w : ℕ → ℚ) (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat (liaHistory (paperDP T)) w) :
    ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) → ∀ x,
      v.ValuesAt (X n) x →
        ∃ z, v.ValuesAt (indicatorProductLUV
            (paperDeferredWeightQuoteCode T f w weight_generable weight_mem) φ n) z ∧
          |z - x * w (f n)| ≤ 0 := by
  intro n v hv x hx
  refine ⟨x * (w (f n) : ℝ), ?_, by simp⟩
  have hxeq : x = v.payout (φ n) := hx.eq ((hind n).valuesAt hv)
  have h := indicatorProductLUV_valuesAt (paperQuotationPresentation T)
    (paperDeferredWeightQuoteCode T f w weight_generable weight_mem) φ n v hv
  rwa [hxeq]

end PeanoMinus

/-! ## `thm:lp` and its arithmetic strength

The paradox-resistance endpoint is the one place on this lane where the diagonal is built,
and Foundation's `parameterized_diagonal₁` is stated over `𝗜𝚺₁`.  Since `𝗜𝚺₁ ⪯ T` implies
`𝗣𝗔⁻ ⪯ T` by instance (`Arithmetic/Schemata.lean`), carrying both would put a redundant pair
in the elaborated signature, so the declaration sits outside the `𝗣𝗔⁻` section above and
recovers the weaker instance in its proof term, where `paperLIA`/`paperDP_hworld` need
it.  `omit` cannot do this job: instance search reaches a section variable that is still in
the local context, so the binder has to be out of scope rather than merely unlisted. -/

variable [T.Δ₁] [Entailment.Consistent T]

/-- `thm:lp` (paradox resistance), unconditional over `LIA`.  The named market program,
its self-referential public atom, and the matching FFL parameterized fixed point are all
constructed internally.
`𝗜𝚺₁ ⪯ T` is the one genuinely load-bearing arithmetic strengthening left on this lane: the
diagonal reaches Foundation's `parameterized_diagonal₁`, which is stated over `𝗜𝚺₁`.  It is
carried *in place of* the `[𝗣𝗔⁻ ⪯ T]` of the section above, not beside it — see the section
note.  The elaborated signature therefore carries no redundant pair.
The tolerance width the interior construction needs is *not* a premise: the paper states no
`δ` at this node, and `width` occurs nowhere in the conclusion, so the endpoint discharges it
internally at the paper's own tolerance sequence `2⁻ⁿ` (`digitRatCodes_two_pow_inv`).
Paper node: `thm:lp` -/
theorem lic_paradox_resistance_ofDiagonal_unconditional [𝗜𝚺₁ ⪯ T]
    (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1) :
    (fun n => liaHistory (paperDP T) n
      ((paperDiagonalQuoteCode T p).toBooleanQuoteCode.sentence n)) ≈ₙ
      fun _ => (p : ℝ) :=
  haveI : 𝗣𝗔⁻ ⪯ T := inferInstance
  haveI := paperLIA T
  lic_paradox_resistance_ofDiagonal (paperQuotationPresentation T) (liaHistory (paperDP T))
    (paperMarketComputation T) p hp0 hp1
    (fun n => (((2 ^ n : ℕ) : ℚ))⁻¹) digitRatCodes_two_pow_inv
    (fun n => by positivity)
    (Filter.Tendsto.congr (fun n => by push_cast; rw [inv_pow])
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num :
        ((2 : ℝ)⁻¹) < 1)))
    (paperDP_hworld T)

end LogicalInduction
