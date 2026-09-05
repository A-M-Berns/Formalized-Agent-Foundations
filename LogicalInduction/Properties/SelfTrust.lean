import LogicalInduction.Properties.ExpectationAffine
import LogicalInduction.Properties.Basic
import LogicalInduction.Framework.WriteOut

/-!
# Self-Trust

Renders §4.12: `thm:cee` (tex:2045), `thm:ceu` (tex:2056), `thm:ccee` (tex:2068) and
`thm:st` (tex:2092).  Two definitions the paper states in §4.3 are rendered here as well:
`def:deferralfunc` (tex:1240), whose efficiency clause goes through the clocked interpreter
(`dd:fuel`) and which `succDeferral` inhabits, and `def:ctsind` (tex:1174) in its
real-valued form `ctsInd` — the feature-valued rendering of the same definition is
`calibrationIndicator` in `Properties/Calibration.lean`.

These theorems quantify over *quoted* sentences (`⌜𝔼_{f(n)}(X_n)⌝`, `⌜P_{f(n)}(φ_n)⌝`) —
first-order reflection the propositional `Sentence` cannot express.  Quotation is therefore
modeled relationally, in the way that keeps the statements non-vacuous:

* **Quoted objects are relational.** Each quoted expression enters as an *arbitrary* `LUV`
  family `Y : ℕ → LUV` constrained by a linkage hypothesis (`PCWorld.ValuesAt`), never as
  a canonical construction — building a representative here would silently pre-discharge
  the very learning content the theorem asserts.
* **Reflection uses the completed theory.** A value assertion quantifies over every rational
  threshold, so no finite deductive stage can in general contain its entire infinite
  threshold diagram.  The faithful propositional translation therefore asks every world
  consistent with the completed theory to value the quote correctly.  The explicit inductor
  construction discharges this pointwise: each true or false threshold computation is
  eventually proved and enters `D`.

**Residual type-`(c)` disclosure:** the linkage hypotheses import the paper's entire
"quoting + Θ-represents-computations" mechanism; their principled witness is the explicit
inductor construction in `Construction/Witnesses/QuotationAffine.lean`.

Market timing is a separate, load-bearing obligation, and the fixed-portfolio section below
is where it is exposed: `AffineQuotePortfolio` carries the portfolio fixed on day `n`, its
uniform emitter, its normalization and its bounded prices, and `AffineQuoteEq` /
`AffineQuoteGE` add the deferred-day coherence `thm:exppolymax` needs.  No future-knowing
deductive process is introduced.

`AffineQuotePortfolio.preemptive_asympEq_zero` and `preemptive_asympGE_zero` are the
reusable `thm:affpolymax` transport that the four endpoints below run through, and
`gap_asympEq_zero_of_diagonal` divides the normalization back out.  That last step is
shared: the same-day certificates in `Properties/Introspection.lean` reach a vanishing
diagonal price by Affine Provability Induction instead, and then divide out through it.

Each of the four theorems is stated against one bundled certificate —
`ExpectedFutureExpectationQuote`, `FuturePriceQuote`, `ConditionalExpectationQuote`,
`SelfTrustQuote` — inhabited over the constructed inductor in
`Construction/Witnesses/QuotationAffine.lean`.  `thm:ccee`'s vanishing product slack is
carried explicitly as `ConditionalExpectationQuote.slack` (`dd:mesh`).  Those four
structures and the three portfolio structures are `#assert_fields`-frozen.
-/

namespace LogicalInduction

open Filter Topology

/-! ## Deferral functions -/

/-- `def:deferralfunc`. A **deferral function**: `f n > n`, and `f` is computable within
fuel polynomial **in `f n`** (the paper's "time polynomial in `f(n)`" — deliberately
weaker than poly-in-`n`, since `f` may grow fast), rendered through the clocked
interpreter (`dd:fuel`).
Paper node: `def:deferralfunc` -/
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

/-- **Non-vacuity of `def:deferralfunc`** — kind `N+` non-vacuity witness.  The successor
`n ↦ n + 1` is a deferral function: it defers (`n < n + 1`) and `Nat.Partrec.Code.succ`
returns it within one step of the clocked interpreter, well inside the polynomial-in-`f n`
budget.  Every `DeferralFunction` binder in this file and in the `thm:cee` / `thm:ceu` /
`thm:ccee` / `thm:st` endpoints is therefore inhabited.
Provenance: (a) derived in-project. -/
def succDeferral : DeferralFunction where
  f := (· + 1)
  lt n := Nat.lt_succ_self n
  code := Nat.Partrec.Code.succ
  fueled := ⟨1, 1, fun n => by simp [Nat.Partrec.Code.evaln]⟩

/-! ## The continuous threshold indicator -/

/-- `def:ctsind`, real-valued form: the continuous threshold indicator
`ctsind_δ(x > y)` — `0` at `x ≤ y`, linear on `(y, y+δ]`, `1` beyond. -/
noncomputable def ctsInd (δ : ℚ) (x y : ℝ) : ℝ :=
  min 1 (max 0 ((x - y) / (δ : ℝ)))

/-- The continuous threshold gate always lies in `[0,1]` when its width is positive. -/
lemma ctsInd_mem_Icc (δ : ℚ) (x y : ℝ) :
    ctsInd δ x y ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_min zero_le_one (le_max_left _ _)
  · exact min_le_left _ _

/-- The continuous threshold gate is fully on once its first argument exceeds the second
by at least the positive rational width. -/
lemma ctsInd_eq_one_of_le_sub (δ : ℚ) (x y : ℝ) (hδ : 0 < δ)
    (hgap : (δ : ℝ) ≤ x - y) : ctsInd δ x y = 1 := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hratio : 1 ≤ (x - y) / (δ : ℝ) := (le_div_iff₀ hδR).2 (by linarith)
  have hzero : 0 ≤ (x - y) / (δ : ℝ) := zero_le_one.trans hratio
  unfold ctsInd
  rw [max_eq_right hzero, min_eq_left hratio]

/-! ## Fixed-portfolio quote coherence

The paper's `thm:exppolymax` step does not compare two independently regenerated
day-indexed expectation grids.  It fixes one affine portfolio on day `n` and reprices
*that same portfolio* on the deferred day `f n`, so coherence at the later day gives `D n`
no oracle access to future prices.  The structures below expose exactly that boundary; the
individual fields are documented at the structures.
-/

/-- A polynomial, normalized fixed-portfolio presentation of a real-valued gap.
Paper node: `thm:er` -/
structure AffineQuotePortfolio (P : History) (gap : ℕ → ℝ) where
  /-- The portfolio fixed on day `n` and retained unchanged when priced later. -/
  family : ℕ → AffineCombination
  /-- Uniform syntax/emission certificate for the family. -/
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
(`thm:er`/`thm:epr` plus encoding coherence), and is the obligation that a concrete
quotation mechanism must discharge.
Paper node: `thm:er` -/
structure AffineQuoteEq (P : History) (f : DeferralFunction) (gap : ℕ → ℝ)
    extends AffineQuotePortfolio P gap where
  future_coherent :
    AsympEq (fun n => (family n).price P (f n)) (fun _ => 0)

/-- One-sided quote coherence, used by `thm:st`: the fixed portfolio's deferred-day
price is asymptotically nonnegative.
Paper node: `thm:st` -/
structure AffineQuoteGE (P : History) (f : DeferralFunction) (gap : ℕ → ℝ)
    extends AffineQuotePortfolio P gap where
  future_coherent :
    AsympGE (fun n => (family n).price P (f n)) (fun _ => 0)

/-- Complete quote certificate for `thm:cee`: compact source/quote syntax, delayed
world semantics, and the fixed-portfolio cross-grid law are one explicit trust object.
Paper node: `thm:cee` -/
structure ExpectedFutureExpectationQuote (P : History) (DP : DeductiveProcess)
    (f : DeferralFunction) (X Y : ℕ → LUV) where
  source_codes : LUV.RpnThresholdCodeSeq X
  quote_codes : LUV.RpnThresholdCodeSeq Y
  reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    v.ValuesAt (Y n) ((X n).expect P (f n))
  affine : AffineQuoteEq P f (fun n => (X n).expect P n - (Y n).expect P n)

/-- Complete quote certificate for `thm:ceu`.
Paper node: `thm:ceu` -/
structure FuturePriceQuote (P : History) (DP : DeductiveProcess)
    (f : DeferralFunction) (φ : ℕ → Sentence) (Y : ℕ → LUV) where
  sentence_codes : BigSentenceCodes φ
  quote_codes : LUV.RpnThresholdCodeSeq Y
  reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    v.ValuesAt (Y n) (P (f n) (φ n))
  affine : AffineQuoteEq P f (fun n => P n (φ n) - (Y n).expect P n)

/-- Complete weighted-product quote certificate for `thm:ccee`.

**Disclosed type-`(c)` modeling substitution (`dd:mesh`).**  The left quoted product is
required to reflect `x · w (f n)` only to within a *vanishing* slack `slack n`, not
exactly.  This is what makes the theorem available for an arbitrary e.c. source family
`X`, as the paper states it: an exact product LUV would have to carry the threshold
`⌜X > r / w (f n)⌝`, whose emitter would need the *value* of the deferred weight, which
is unavailable (the `dd:mesh` construction in
`Construction/Witnesses/QuoteCodeOfMarket.lean` is where this is worked out).
The general-source construction instead reads the deferred weight through its own
threshold atoms on a width-`n+1` mesh, which pins the product to within `1/(n+1)`.  The
exact-reflection case is the `slack = 0` instance and is still inhabited (the indicator
source), so this is a genuine weakening of the certificate, not a vacuous one.
Paper node: `thm:ccee` -/
structure ConditionalExpectationQuote (P : History) (DP : DeductiveProcess)
    (f : DeferralFunction) (X Z Z' : ℕ → LUV) (w : ℕ → ℚ) where
  weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1
  weight_generable : PGenerableRat P w
  source_codes : LUV.RpnThresholdCodeSeq X
  left_codes : LUV.RpnThresholdCodeSeq Z
  right_codes : LUV.RpnThresholdCodeSeq Z'
  /-- The per-day reflection slack of the left quoted product. -/
  slack : ℕ → ℝ
  slack_tendsto : Tendsto slack atTop (𝓝 0)
  source_valued : ∀ n (v : PCWorld),
    v.ConsistentWithTheory DP → ∃ x, v.ValuesAt (X n) x
  left_reflected : ∀ n (v : PCWorld),
    v.ConsistentWithTheory DP → ∀ x,
      v.ValuesAt (X n) x → ∃ z, v.ValuesAt (Z n) z ∧ |z - x * w (f n)| ≤ slack n
  right_reflected : ∀ n (v : PCWorld),
    v.ConsistentWithTheory DP →
      v.ValuesAt (Z' n) ((X n).expect P (f n) * w (f n))
  affine : AffineQuoteEq P f
    (fun n => (Z n).expect P n - (Z' n).expect P n)

/-- Complete confidence/product quote certificate for `thm:st`.

The confidence threshold `p` enters as a **P-generable** rational sequence (`def:ece`),
matching the paper's `thm:st`: `p` may vary continuously with the market's own prices, and
the trader carries it as a feature *expression* rather than as a day-`n` numeral.  The
paper's e.c. rational sequences are the special case `ratCodeFeature`, and `def:ece`'s
emission field is **write-out** metered, so that special case reaches the paper's own
class: `PGenerableRat.ofDigitRatCodes` admits `p n = 1 − 2⁻ⁿ` and every other sequence
whose codes are exponential but polynomially writable (`pGenerableRat_two_pow_inv`).

Both quoted LUVs carry their threshold families in the **write-out** class
(`LUV.BigThresholdCodeSeq`), the same meter `sentence_codes` uses and the one the rest of
the day-indexed surface carries: polynomially many emitted tokens, individual token values
unbounded.  Nothing on this lane opens a threshold certificate as value-bounded emission
data — every consumer either reindexes it or hands it to `AffineCombination.PolySequence`,
whose `sentence_poly` field is already write-out metered.
Paper node: `thm:st` -/
structure SelfTrustQuote (P : History) (DP : DeductiveProcess)
    (f : DeferralFunction) (φ : ℕ → Sentence) (δ p : ℕ → ℚ)
    (A B : ℕ → LUV) where
  delta_pos : ∀ n, 0 < δ n
  probability_mem : ∀ n, 0 ≤ p n ∧ p n ≤ 1
  sentence_codes : BigSentenceCodes φ
  probability_generable : PGenerableRat P p
  product_codes : LUV.BigThresholdCodeSeq A
  confidence_codes : LUV.BigThresholdCodeSeq B
  confidence_reflected : ∀ n (v : PCWorld),
    v.ConsistentWithTheory DP →
      v.ValuesAt (B n) (ctsInd (δ n) (P (f n) (φ n)) (p n))
  product_reflected : ∀ n (v : PCWorld),
    v.ConsistentWithTheory DP →
      v.ValuesAt (A n)
        (v.payout (φ n) * ctsInd (δ n) (P (f n) (φ n)) (p n))
  affine : AffineQuoteGE P f
    (fun n => (A n).expect P n - (p n : ℝ) * (B n).expect P n)

/-! ## Preemptive transport

`thm:affpolymax` applied to a fixed portfolio: a polynomial affine family with bounded
magnitude has no preemptive price gaps, so a portfolio worth asymptotically nothing when
repriced on its deferred day already has an asymptotically zero diagonal price.
`gap_asympEq_zero_of_diagonal` then divides the portfolio's positive rational normalization
back out, returning the quoted gap itself.
-/

namespace AffineQuotePortfolio

private lemma price_le_futureHigh {P : History} {gap : ℕ → ℝ}
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

private lemma futureLow_le_price {P : History} {gap : ℕ → ℝ}
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
lemma preemptive_asympEq_zero {P : History} {gap : ℕ → ℝ}
    (q : AffineQuotePortfolio P gap)
    (DP : DeductiveProcess) [IsLogicalInductor P DP] (f : DeferralFunction)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hfuture : AsympEq (fun n => (q.family n).price P (f n)) (fun _ => 0)) :
    AsympEq (fun n => (q.family n).price P n) (fun _ => 0) := by
  rw [asympEq_iff_asympLE_asympGE]
  have hgaps := q.poly.noPreemptiveGaps P DP q.magnitude_le_one hcons
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

/-- Divide the portfolio's positive rational normalization out of an asymptotically
vanishing diagonal price, recovering the quoted gap itself.  This is the last step of every
two-sided quotation endpoint, here and in `Properties/Introspection.lean`; the callers
differ only in which result supplies the vanishing diagonal price. -/
lemma gap_asympEq_zero_of_diagonal {P : History} {gap : ℕ → ℝ}
    (q : AffineQuotePortfolio P gap)
    (hdiag : AsympEq (fun n => (q.family n).price P n) (fun _ => 0)) :
    AsympEq gap (fun _ => 0) := by
  rw [asympEq_iff_eventuallyWithin]
  intro ε hε
  have hs : (0 : ℝ) < q.scale := by exact_mod_cast q.scale_pos
  have hzero := asympEq_iff_eventuallyWithin.1 hdiag ((q.scale : ℝ) * ε) (mul_pos hs hε)
  filter_upwards [hzero] with n hn
  rw [q.current_price, sub_zero, abs_mul, abs_of_pos hs] at hn
  simpa only [sub_zero] using (mul_le_mul_iff_of_pos_left hs).mp hn

/-- Remove the positive normalization from a two-sided fixed-portfolio certificate. -/
lemma gap_asympEq_zero {P : History} {gap : ℕ → ℝ}
    (q : AffineQuotePortfolio P gap)
    (DP : DeductiveProcess) [IsLogicalInductor P DP] (f : DeferralFunction)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hfuture : AsympEq (fun n => (q.family n).price P (f n)) (fun _ => 0)) :
    AsympEq gap (fun _ => 0) :=
  q.gap_asympEq_zero_of_diagonal (q.preemptive_asympEq_zero DP f hcons hfuture)

/-- One-sided version of the preemptive transport. -/
lemma preemptive_asympGE_zero {P : History} {gap : ℕ → ℝ}
    (q : AffineQuotePortfolio P gap)
    (DP : DeductiveProcess) [IsLogicalInductor P DP] (f : DeferralFunction)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hfuture : AsympGE (fun n => (q.family n).price P (f n)) (fun _ => 0)) :
    AsympGE (fun n => (q.family n).price P n) (fun _ => 0) := by
  intro ε hε
  have hgaps := q.poly.noPreemptiveGaps P DP q.magnitude_le_one hcons
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
lemma gap_asympGE_zero {P : History} {gap : ℕ → ℝ}
    (q : AffineQuotePortfolio P gap)
    (DP : DeductiveProcess) [IsLogicalInductor P DP] (f : DeferralFunction)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hfuture : AsympGE (fun n => (q.family n).price P (f n)) (fun _ => 0)) :
    AsympGE gap (fun _ => 0) := by
  intro ε hε
  have hs : (0 : ℝ) < q.scale := by exact_mod_cast q.scale_pos
  have hzero := q.preemptive_asympGE_zero DP f hcons hfuture
    ((q.scale : ℝ) * ε) (mul_pos hs hε)
  filter_upwards [hzero] with n hn
  rw [q.current_price] at hn
  nlinarith

end AffineQuotePortfolio

/-! ## The four Self-Trust statements

Common shape: `f` a deferral function, completed-theory semantics for each quoted family,
and a fixed-portfolio coherence certificate.  The semantic fields are pointwise consequences
of arithmetic representation; the portfolio certificate separately exposes the paper's
cross-grid `thm:exppolymax` obligation. -/

/-- **Expected Future Expectations** (`thm:cee`): `𝔼ₙ(Xₙ) ≈ₙ 𝔼ₙ(⌜𝔼_{f(n)}(Xₙ)⌝)`.
`Y n` is the quoted future expectation: every completed-theory world values it
at the actual day-`f n` expectation of `X n`.
Paper node: `thm:cee` -/
theorem lic_expected_future_expectations (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (f : DeferralFunction) (X Y : ℕ → LUV)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hquote : ExpectedFutureExpectationQuote P DP f X Y) :
    AsympEq (fun n => (X n).expect P n) (fun n => (Y n).expect P n) := by
  simpa only [AsympEq, sub_zero] using
    hquote.affine.toAffineQuotePortfolio.gap_asympEq_zero DP f hcons
      hquote.affine.future_coherent

/-- **No Expected Net Update** (`thm:ceu`): `Pₙ(φₙ) ≈ₙ 𝔼ₙ(⌜P_{f(n)}(φₙ)⌝)`.
`Y n` is the quoted future price: every completed-theory world values it at the actual
day-`f n` price of `φ n`.
Paper node: `thm:ceu` -/
theorem lic_no_expected_net_update (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (f : DeferralFunction) (φ : ℕ → Sentence)
    (Y : ℕ → LUV)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hquote : FuturePriceQuote P DP f φ Y) :
    AsympEq (fun n => P n (φ n)) (fun n => (Y n).expect P n) := by
  simpa only [AsympEq, sub_zero] using
    hquote.affine.toAffineQuotePortfolio.gap_asympEq_zero DP f hcons
      hquote.affine.future_coherent

/-- **No Expected Net Update under Conditionals** (`thm:ccee`):
`𝔼ₙ(⌜Xₙ·w_{f(n)}⌝) ≈ₙ 𝔼ₙ(⌜𝔼_{f(n)}(Xₙ)·w_{f(n)}⌝)`, for a weight sequence `w` in
`[0,1]`. `Z n` and `Z' n` are the two quoted products, linked pointwise to the values of
`X n`: in any world valuing `X n` at `x`, `Z n` is valued within the certificate's
vanishing slack of `x · w (f n)`, and `Z' n` at the (world-independent)
`𝔼_{f n}(Xₙ) · w (f n)`.

The bundled certificate records both `[0,1]` membership and paper-side P-generability
(`def:ece`) of `w`, and carries the left-product slack (disclosed type-`(c)`; see
`ConditionalExpectationQuote`).
Paper node: `thm:ccee` -/
theorem lic_no_expected_net_update_conditional (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (f : DeferralFunction) (X Z Z' : ℕ → LUV)
    (w : ℕ → ℚ)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hquote : ConditionalExpectationQuote P DP f X Z Z' w) :
    AsympEq (fun n => (Z n).expect P n) (fun n => (Z' n).expect P n) := by
  simpa only [AsympEq, sub_zero] using
    hquote.affine.toAffineQuotePortfolio.gap_asympEq_zero DP f hcons
      hquote.affine.future_coherent

/-- **Self-Trust** (`thm:st`):
`𝔼ₙ(⌜1(φₙ)·ctsind_{δₙ}(P_{f(n)}(φₙ) > pₙ)⌝) ≳ₙ pₙ · 𝔼ₙ(⌜ctsind_{δₙ}(…)⌝)` — the
inductor's current expectation of `φₙ`, restricted to the (fuzzy) event that its future
self will be confident in `φₙ`, is at least `pₙ` times its expectation of that event.

`B n` is the quoted indicator of future confidence — valued in every completed-theory
world at the actual `ctsind` of the day-`f n` price against threshold `p n` — and `A n`
the quoted product `1(φₙ)·B n`, valued at `payout(φₙ)` times that indicator (the value of
`1(φ)` in `v` **is** `v`'s payout on `φ`, which is what makes the conclusion genuinely
world-dependent).  `p` is P-generable (`def:ece`), as in the paper — not restricted to
market-independent e.c. rational sequences.
Paper node: `thm:st` -/
theorem lic_self_trust (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (f : DeferralFunction) (φ : ℕ → Sentence)
    (δ p : ℕ → ℚ) (A B : ℕ → LUV)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hquote : SelfTrustQuote P DP f φ δ p A B) :
    AsympGE (fun n => (A n).expect P n) (fun n => (p n : ℝ) * (B n).expect P n) := by
  have hgap := hquote.affine.toAffineQuotePortfolio.gap_asympGE_zero DP f hcons
    hquote.affine.future_coherent
  intro ε hε
  filter_upwards [hgap ε hε] with n hn
  linarith

end LogicalInduction
