/-
# Self-Trust — `thm:cee`, `thm:ceu`, `thm:ccee`, `thm:st` (statement audit)

Paper §4.12 (`main.tex` 2045–2092). These theorems quantify over *quoted* sentences
(`⌜𝔼_{f(n)}(X_n)⌝`, `⌜P_{f(n)}(φ_n)⌝`) — first-order reflection our propositional
`Sentence` cannot express. Per the G2 decision (Anson, 2026-07-11), reflection is modeled
the **non-vacuous way**:

* **Quoted objects are relational.** Each quoted expression enters as an *arbitrary* LUV
  family `Y : ℕ → LUV` constrained by a linkage hypothesis (`PCWorld.ValuesAt`), never as
  a canonical construction — constructing a representative would silently pre-discharge
  the learning content (the D3 general principle).
* **Reflection uses the completed theory.** A value assertion quantifies over every rational
  threshold, so no finite deductive stage can in general contain its entire infinite
  threshold diagram.  The faithful propositional translation therefore asks every world
  consistent with the completed theory to value the quote correctly.  M7's construction
  discharges this pointwise: each true or false threshold computation is eventually proved
  and enters `D`.  Deferred market timing remains a separate, load-bearing obligation in
  `AffineQuoteEq`/`AffineQuoteGE`; no future-knowing deductive process is introduced.

**Residual type-`(c)` (ledgered):** the linkage hypotheses import the paper's entire
"quoting + Θ-represents-computations" mechanism; their principled witness is M7's
construction. Naming caution (roadmap): the deference corpus's "cee" is the paper's
`thm:ceu`.

**M4/M7 repair:** completed-theory hypotheses record the logical semantics of each quote,
while `AffineQuoteEq`/`AffineQuoteGE` supply the operational certificate: one fixed,
uniformly emitted affine portfolio whose later price is coherent.  This separates logical
quotation from the preemptive-learning transport proved here.
-/
import LogicalInduction.Properties.ExpectationAffine
import LogicalInduction.Properties.Basic

namespace LogicalInduction

open Filter Topology

/-! ### `def:deferralfunc` -/

/-- `def:deferralfunc`. A **deferral function**: `f n > n`, and `f` is computable within
fuel polynomial **in `f n`** (the paper's "time polynomial in `f(n)`" — deliberately
weaker than poly-in-`n`, since `f` may grow fast), rendered through the clocked
interpreter (`dd:fuel`). -/
structure DeferralFunction where
  /-- The underlying function. -/
  f : ℕ → ℕ
  /-- `f` defers: `f n > n`. -/
  lt : ∀ n, n < f n
  /-- A code computing `f`. -/
  code : Nat.Partrec.Code
  /-- The code halts within fuel polynomial in `f n`. -/
  fueled : ∃ a k : ℕ, ∀ n,
    Nat.Partrec.Code.evaln (a * (f n + 1) ^ k + a) code n = some (f n)

instance : CoeFun DeferralFunction (fun _ => ℕ → ℕ) := ⟨DeferralFunction.f⟩

/-- `def:ctsind`, real-valued form: the continuous threshold indicator
`ctsind_δ(x > y)` — `0` at `x ≤ y`, linear on `(y, y+δ]`, `1` beyond. -/
noncomputable def ctsInd (δ : ℚ) (x y : ℝ) : ℝ :=
  min 1 (max 0 ((x - y) / (δ : ℝ)))

/-! ### Fixed-portfolio quote coherence

The paper's `thm:exppolymax` step does not compare two independently regenerated
day-indexed expectation grids.  It fixes one affine portfolio on day `n`, and compares
the price of that *same portfolio* on day `n` with its price on the deferred day `f n`.
The certificate below exposes exactly that missing boundary.  It contains the concrete
portfolio family, its uniform polynomial emitter, the normalization used to keep one
unit of affine risk, and the exact identification of its day-`n` price with the quoted
gap.  Coherence is imposed only at the later market day, so it does not give `D n`
oracle access to future prices.
-/

/-- A polynomial, normalized fixed-portfolio presentation of a real-valued gap. -/
structure AffineQuotePortfolio (P : History) (gap : ℕ → ℝ) where
  /-- The portfolio fixed on day `n` and retained unchanged when priced later. -/
  family : ℕ → AffineCombination
  /-- Honest uniform syntax/emission certificate for the family. -/
  poly : AffineCombination.PolySequence family
  /-- Positive rational normalization of the represented gap. -/
  scale : ℚ
  scale_pos : 0 < scale
  /-- Exact current-day interpretation of the fixed portfolio. -/
  current_price : ∀ n, (family n).price P n = (scale : ℝ) * gap n
  /-- Cross-time prices are uniformly bounded, as required by `thm:affpolymax`. -/
  bounded : BoundedAffinePrices family P
  /-- The normalization keeps every component within one unit of affine risk. -/
  magnitude_le_one : ∀ n, (family n).magnitude P ≤ 1

/-- Two-sided quote coherence: the fixed portfolio's actual deferred-day price tends to
zero.  This is the propositional interface for the paper's quoted-expectation reasoning
(`thm:er`/`thm:epr` plus encoding coherence), and is the obligation that M7's concrete
quotation mechanism must discharge. -/
structure AffineQuoteEq (P : History) (f : DeferralFunction) (gap : ℕ → ℝ)
    extends AffineQuotePortfolio P gap where
  future_coherent :
    AsympEq (fun n => (family n).price P (f n)) (fun _ => 0)

/-- One-sided quote coherence, used by `thm:st`: the fixed portfolio's deferred-day
price is asymptotically nonnegative. -/
structure AffineQuoteGE (P : History) (f : DeferralFunction) (gap : ℕ → ℝ)
    extends AffineQuotePortfolio P gap where
  future_coherent :
    AsympGE (fun n => (family n).price P (f n)) (fun _ => 0)

/-- Complete quote certificate for `thm:cee`: compact source/quote syntax, delayed
world semantics, and the fixed-portfolio cross-grid law are one explicit trust object. -/
structure ExpectedFutureExpectationQuote (P : History) (DP : DeductiveProcess)
    (f : DeferralFunction) (X Y : ℕ → LUV) where
  source_codes : LUV.PolyThresholdCodeSeq X
  quote_codes : LUV.PolyThresholdCodeSeq Y
  reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    v.ValuesAt (Y n) ((X n).expect P (f n))
  affine : AffineQuoteEq P f (fun n => (X n).expect P n - (Y n).expect P n)

/-- Complete quote certificate for `thm:ceu`. -/
structure FuturePriceQuote (P : History) (DP : DeductiveProcess)
    (f : DeferralFunction) (φ : ℕ → Sentence) (Y : ℕ → LUV) where
  sentence_codes : PolySentenceCodes φ
  quote_codes : LUV.PolyThresholdCodeSeq Y
  reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    v.ValuesAt (Y n) (P (f n) (φ n))
  affine : AffineQuoteEq P f (fun n => P n (φ n) - (Y n).expect P n)

/-- Complete weighted-product quote certificate for `thm:ccee`. -/
structure ConditionalExpectationQuote (P : History) (DP : DeductiveProcess)
    (f : DeferralFunction) (X Z Z' : ℕ → LUV) (w : ℕ → ℚ) where
  weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1
  weight_generable : PGenerableRat P w
  source_codes : LUV.PolyThresholdCodeSeq X
  left_codes : LUV.PolyThresholdCodeSeq Z
  right_codes : LUV.PolyThresholdCodeSeq Z'
  source_valued : ∀ n (v : PCWorld),
    v.ConsistentWithTheory DP → ∃ x, v.ValuesAt (X n) x
  left_reflected : ∀ n (v : PCWorld),
    v.ConsistentWithTheory DP → ∀ x,
      v.ValuesAt (X n) x → v.ValuesAt (Z n) (x * w (f n))
  right_reflected : ∀ n (v : PCWorld),
    v.ConsistentWithTheory DP →
      v.ValuesAt (Z' n) ((X n).expect P (f n) * w (f n))
  affine : AffineQuoteEq P f
    (fun n => (Z n).expect P n - (Z' n).expect P n)

/-- Complete confidence/product quote certificate for `thm:st`. -/
structure SelfTrustQuote (P : History) (DP : DeductiveProcess)
    (f : DeferralFunction) (φ : ℕ → Sentence) (δ p : ℕ → ℚ)
    (A B : ℕ → LUV) where
  delta_pos : ∀ n, 0 < δ n
  probability_mem : ∀ n, 0 ≤ p n ∧ p n ≤ 1
  sentence_codes : PolySentenceCodes φ
  delta_codes : PolyRatCodes δ
  probability_codes : PolyRatCodes p
  product_codes : LUV.PolyThresholdCodeSeq A
  confidence_codes : LUV.PolyThresholdCodeSeq B
  confidence_reflected : ∀ n (v : PCWorld),
    v.ConsistentWithTheory DP →
      v.ValuesAt (B n) (ctsInd (δ n) (P (f n) (φ n)) (p n))
  product_reflected : ∀ n (v : PCWorld),
    v.ConsistentWithTheory DP →
      v.ValuesAt (A n)
        (v.payout (φ n) * ctsInd (δ n) (P (f n) (φ n)) (p n))
  affine : AffineQuoteGE P f
    (fun n => (A n).expect P n - (p n : ℝ) * (B n).expect P n)

namespace AffineQuotePortfolio

private theorem price_le_futureHigh {P : History} {gap : ℕ → ℝ}
    (q : AffineQuotePortfolio P gap) {n m : ℕ}
    (hnm : n ≤ m) :
    (q.family n).price P m ≤ affineFutureHigh q.family P n := by
  obtain ⟨B, _, hB⟩ := q.bounded
  apply le_csSup
  · refine ⟨B, ?_⟩
    rintro x ⟨j, rfl⟩
    exact (le_abs_self _).trans (hB n (n + j))
  · refine ⟨m - n, ?_⟩
    simpa using congrArg (fun k => (q.family n).price P k) (Nat.add_sub_of_le hnm)

private theorem futureLow_le_price {P : History} {gap : ℕ → ℝ}
    (q : AffineQuotePortfolio P gap) {n m : ℕ}
    (hnm : n ≤ m) :
    affineFutureLow q.family P n ≤ (q.family n).price P m := by
  obtain ⟨B, _, hB⟩ := q.bounded
  apply csInf_le
  · refine ⟨-B, ?_⟩
    rintro x ⟨j, rfl⟩
    linarith [neg_abs_le ((q.family n).price P (n + j)), hB n (n + j)]
  · refine ⟨m - n, ?_⟩
    simpa using congrArg (fun k => (q.family n).price P k) (Nat.add_sub_of_le hnm)

/-- Reusable `thm:affpolymax` transport: if a fixed polynomial affine portfolio is
asymptotically worth zero when repriced on its deferred day, then its diagonal price is
already asymptotically zero. -/
theorem preemptive_asympEq_zero {P : History} {gap : ℕ → ℝ}
    (q : AffineQuotePortfolio P gap)
    (DP : DeductiveProcess) [IsLogicalInductor P DP] (f : DeferralFunction)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hfuture : AsympEq (fun n => (q.family n).price P (f n)) (fun _ => 0)) :
    AsympEq (fun n => (q.family n).price P n) (fun _ => 0) := by
  rw [asympEq_iff_asympLE_asympGE]
  have hgaps := q.poly.noPreemptiveGaps P DP q.magnitude_le_one hP hcons
  constructor
  · intro ε hε
    have hnear := asympEq_iff_eventuallyWithin.1 hfuture (ε / 4) (by linarith)
    have hfutureLow : ∀ᶠ n in atTop, affineFutureLow q.family P n < ε / 2 := by
      filter_upwards [hnear] with n hn
      have hlo := q.futureLow_le_price (f.lt n).le
      simp only [sub_zero] at hn
      have hupper := (abs_le.mp hn).2
      linarith
    have hnot := hgaps.overpriced (ε / 2) ε (by linarith) hfutureLow
    rw [Filter.not_frequently] at hnot
    filter_upwards [hnot] with n hn
    simpa only [Pi.zero_apply, zero_add] using le_of_not_gt hn
  · intro ε hε
    have hnear := asympEq_iff_eventuallyWithin.1 hfuture (ε / 4) (by linarith)
    have hfutureHigh : ∀ᶠ n in atTop, -ε / 2 < affineFutureHigh q.family P n := by
      filter_upwards [hnear] with n hn
      have hhi := q.price_le_futureHigh (f.lt n).le
      simp only [sub_zero] at hn
      have hlower := (abs_le.mp hn).1
      linarith
    have hnot := hgaps.underpriced (-ε) (-ε / 2) (by linarith) hfutureHigh
    rw [Filter.not_frequently] at hnot
    filter_upwards [hnot] with n hn
    have hbound : -ε ≤ (q.family n).price P n := by linarith [le_of_not_gt hn]
    linarith

/-- Remove the positive normalization from a two-sided fixed-portfolio certificate. -/
theorem gap_asympEq_zero {P : History} {gap : ℕ → ℝ}
    (q : AffineQuotePortfolio P gap)
    (DP : DeductiveProcess) [IsLogicalInductor P DP] (f : DeferralFunction)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hfuture : AsympEq (fun n => (q.family n).price P (f n)) (fun _ => 0)) :
    AsympEq gap (fun _ => 0) := by
  rw [asympEq_iff_eventuallyWithin]
  intro ε hε
  have hs : (0 : ℝ) < q.scale := by exact_mod_cast q.scale_pos
  have hzero := asympEq_iff_eventuallyWithin.1
    (q.preemptive_asympEq_zero DP f hP hcons hfuture)
    ((q.scale : ℝ) * ε) (mul_pos hs hε)
  filter_upwards [hzero] with n hn
  rw [q.current_price, sub_zero, abs_mul, abs_of_pos hs] at hn
  simpa only [sub_zero] using (mul_le_mul_iff_of_pos_left hs).mp hn

/-- One-sided version of the preemptive transport. -/
theorem preemptive_asympGE_zero {P : History} {gap : ℕ → ℝ}
    (q : AffineQuotePortfolio P gap)
    (DP : DeductiveProcess) [IsLogicalInductor P DP] (f : DeferralFunction)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hfuture : AsympGE (fun n => (q.family n).price P (f n)) (fun _ => 0)) :
    AsympGE (fun n => (q.family n).price P n) (fun _ => 0) := by
  intro ε hε
  have hgaps := q.poly.noPreemptiveGaps P DP q.magnitude_le_one hP hcons
  have hfutureHigh : ∀ᶠ n in atTop, -ε / 2 < affineFutureHigh q.family P n := by
    filter_upwards [hfuture (ε / 4) (by linarith)] with n hn
    have hhi := q.price_le_futureHigh (f.lt n).le
    linarith
  have hnot := hgaps.underpriced (-ε) (-ε / 2) (by linarith) hfutureHigh
  rw [Filter.not_frequently] at hnot
  filter_upwards [hnot] with n hn
  have hbound : -ε ≤ (q.family n).price P n := by linarith [le_of_not_gt hn]
  linarith

/-- Remove the positive normalization from a one-sided fixed-portfolio certificate. -/
theorem gap_asympGE_zero {P : History} {gap : ℕ → ℝ}
    (q : AffineQuotePortfolio P gap)
    (DP : DeductiveProcess) [IsLogicalInductor P DP] (f : DeferralFunction)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hfuture : AsympGE (fun n => (q.family n).price P (f n)) (fun _ => 0)) :
    AsympGE gap (fun _ => 0) := by
  intro ε hε
  have hs : (0 : ℝ) < q.scale := by exact_mod_cast q.scale_pos
  have hzero := q.preemptive_asympGE_zero DP f hP hcons hfuture
    ((q.scale : ℝ) * ε) (mul_pos hs hε)
  filter_upwards [hzero] with n hn
  rw [q.current_price] at hn
  nlinarith

end AffineQuotePortfolio

/-! ### The four Self-Trust statements

Common shape: `f` a deferral function, completed-theory semantics for each quoted family,
and a fixed-portfolio coherence certificate.  The semantic fields are pointwise consequences
of arithmetic representation; the portfolio certificate separately exposes the paper's
cross-grid `thm:exppolymax` obligation. -/

/-- **Expected Future Expectations** (`thm:cee`): `𝔼ₙ(Xₙ) ≈ₙ 𝔼ₙ(⌜𝔼_{f(n)}(Xₙ)⌝)`.
`Y n` is the quoted future expectation: every completed-theory world values it
at the actual day-`f n` expectation of `X n`. -/
theorem lic_expected_future_expectations (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (f : DeferralFunction) (X Y : ℕ → LUV)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hquote : ExpectedFutureExpectationQuote P DP f X Y) :
    AsympEq (fun n => (X n).expect P n) (fun n => (Y n).expect P n) := by
  simpa only [AsympEq, sub_zero] using
    hquote.affine.toAffineQuotePortfolio.gap_asympEq_zero DP f hP hcons
      hquote.affine.future_coherent

/-- **No Expected Net Update** (`thm:ceu`): `Pₙ(φₙ) ≈ₙ 𝔼ₙ(⌜P_{f(n)}(φₙ)⌝)`.
`Y n` is the quoted future price: every world consistent with `D (r n)` values it at the
actual day-`f n` price of `φ n`. (Deference-corpus name: "cee".) -/
theorem lic_no_expected_net_update (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (f : DeferralFunction) (φ : ℕ → Sentence)
    (Y : ℕ → LUV)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hquote : FuturePriceQuote P DP f φ Y) :
    AsympEq (fun n => P n (φ n)) (fun n => (Y n).expect P n) := by
  simpa only [AsympEq, sub_zero] using
    hquote.affine.toAffineQuotePortfolio.gap_asympEq_zero DP f hP hcons
      hquote.affine.future_coherent

/-- **No Expected Net Update under Conditionals** (`thm:ccee`):
`𝔼ₙ(⌜Xₙ·w_{f(n)}⌝) ≈ₙ 𝔼ₙ(⌜𝔼_{f(n)}(Xₙ)·w_{f(n)}⌝)`, for a weight sequence `w` in
`[0,1]`. `Z n` and `Z' n` are the two quoted products, linked pointwise to the values of
`X n`: in any world valuing `X n` at `x`, `Z n` is valued at `x · w (f n)`, and `Z' n` at
the (world-independent) `𝔼_{f n}(Xₙ) · w (f n)`.

The bundled certificate records both `[0,1]` membership and paper-side P-generability
(`def:pgen`) of `w`. -/
theorem lic_no_expected_net_update_conditional (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (f : DeferralFunction) (X Z Z' : ℕ → LUV)
    (w : ℕ → ℚ)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hquote : ConditionalExpectationQuote P DP f X Z Z' w) :
    AsympEq (fun n => (Z n).expect P n) (fun n => (Z' n).expect P n) := by
  simpa only [AsympEq, sub_zero] using
    hquote.affine.toAffineQuotePortfolio.gap_asympEq_zero DP f hP hcons
      hquote.affine.future_coherent

/-- **Self-Trust** (`thm:st`):
`𝔼ₙ(⌜1(φₙ)·ctsind_{δₙ}(P_{f(n)}(φₙ) > pₙ)⌝) ≳ₙ pₙ · 𝔼ₙ(⌜ctsind_{δₙ}(…)⌝)` — the
inductor's current expectation of `φₙ`, restricted to the (fuzzy) event that its future
self will be confident in `φₙ`, is at least `pₙ` times its expectation of that event.

`B n` is the quoted indicator of future confidence — valued in every completed-theory
world at the actual `ctsind` of the day-`f n` price against threshold `p n` — and `A n`
the quoted product `1(φₙ)·B n`, valued at `payout(φₙ)` times that indicator (the value of
`1(φ)` in `v` **is** `v`'s payout on `φ`, which is what makes the conclusion genuinely
world-dependent). -/
theorem lic_self_trust (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (f : DeferralFunction) (φ : ℕ → Sentence)
    (δ p : ℕ → ℚ) (A B : ℕ → LUV)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hquote : SelfTrustQuote P DP f φ δ p A B) :
    AsympGE (fun n => (A n).expect P n) (fun n => (p n : ℝ) * (B n).expect P n) := by
  have hgap := hquote.affine.toAffineQuotePortfolio.gap_asympGE_zero DP f hP hcons
    hquote.affine.future_coherent
  intro ε hε
  filter_upwards [hgap ε hε] with n hn
  linarith

#print axioms AffineQuotePortfolio.preemptive_asympEq_zero
#print axioms AffineQuotePortfolio.preemptive_asympGE_zero
#print axioms lic_expected_future_expectations
#print axioms lic_no_expected_net_update
#print axioms lic_no_expected_net_update_conditional
#print axioms lic_self_trust

end LogicalInduction
