import LogicalInduction.Properties.ExpectationAffine
import LogicalInduction.Properties.Support.Exploitation
import LogicalInduction.Framework.Emission.WriteOut
import LogicalInduction.Framework.Machine.Ruler

/-!
# Self-Trust

Renders §4.12: `thm:cee` (tex:2045), `thm:ceu` (tex:2056), `thm:ccee` (tex:2068) and
`thm:st` (tex:2092).  Two definitions the paper states in §4.3 are rendered here as well:
`def:deferralfunc` (tex:1240), whose efficiency clause is the machine-metered graph test
`DeferralFunction.graph_fp` and which `succDeferral` and `doublingDeferral` inhabit (the
second at `n ↦ 2 ^ n`, so the fast-growing regime the output-sensitive clause exists to admit
is inhabited too, and by a schedule `not_polyFueled_doublingDeferral` shows no whole-value
fuel clock could have certified) — with
`DeferralFunction.tendsto_atTop` and `DeferralFunction.graphFlag_ruler`, the two facts every
consumer of a deferral function opens it by, and the day-bounded schedule `scheduledValue` /
`scheduledMatch` / `deadlineRun` that is the only thing a machine can actually test the
undecidable deadline with — and `def:ctsind` (tex:1174) in its
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
inductor construction in `Construction/Quotation/Packages.lean`.

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
`Construction/Quotation/Packages.lean`.  `thm:ccee`'s vanishing product slack is
carried explicitly as `ConditionalExpectationQuote.slack` (`dd:mesh`).  Those four
structures and the three portfolio structures are `#assert_fields`-frozen.

-/

namespace LogicalInduction

open Filter Topology

/-! ## Deferral functions -/

/-- `def:deferralfunc`. A **deferral function**: `f n > n`, and `f` is computed within time
polynomial **in `f n`** (the paper's "time polynomial in `f(n)`" — deliberately weaker than
poly-in-`n`, since `f` may grow fast).

The efficiency clause is rendered **at the machine model**, as the paper's own
output-sensitive condition read on the input that carries it: the *graph* of `f` is decided
in polynomial time on the unary pair `⟨n, m⟩`, whose length is `Nat.pair n m ≥ m`, so "time
polynomial in the input length" *is* "time polynomial in the candidate value `m`".  The
answer is the repo's unary flag convention — one mark when `f n = m`, none otherwise.

The two readings are equivalent.  From a program computing `f n` within `h (f n)` steps,
decide the graph at `⟨n, m⟩` by running it for `h m` steps and comparing, which is
polynomial in the pair's length.  Conversely, from the graph decider compute `f n` by
testing `m = n + 1, n + 2, …` until the flag fires: each test is polynomial in `m ≤ f n`
and there are at most `f n` of them, so the search is polynomial in `f n`.  Only the first
direction is used below — every consumer reads the day-bounded schedule off the graph.
Paper node: `def:deferralfunc` -/
structure DeferralFunction where
  /-- The underlying function. -/
  f : ℕ → ℕ
  /-- `f` defers: `f n > n`. -/
  lt : ∀ n, n < f n
  /-- The graph of `f` is decided in polynomial time on the unary pair `⟨n, m⟩`. -/
  graph_fp : ∃ G ∈ Complexity.FP, ∀ n m : ℕ,
    G (List.replicate (Nat.pair n m) true)
      = List.replicate (if f n = m then 1 else 0) false

instance : CoeFun DeferralFunction (fun _ => ℕ → ℕ) := ⟨DeferralFunction.f⟩

/-- Strict deferral tends to infinity even when it grows too quickly to be polynomial in
its source index. -/
lemma DeferralFunction.tendsto_atTop (f : DeferralFunction) :
    Tendsto f atTop atTop := by
  apply tendsto_atTop_atTop.2
  intro N
  exact ⟨N, fun n hn ↦ hn.trans (f.lt n).le⟩

/-- The graph flag of `f` at the paired index `⟨n, m⟩`: one mark when `f n = m`. -/
def DeferralFunction.graphFlag (f : DeferralFunction) (z : ℕ) : ℕ :=
  if f z.unpair.1 = z.unpair.2 then 1 else 0

/-- **The deferral clock.**  `DeferralFunction.graph_fp` states the polynomial-time graph
test as a bare `Complexity.FP` membership on the unary pair; this is the same fact in the
`UnaryRuler` spelling, which is how every consumer of the schedule below reads it.  No
consumer re-derives the composition with the pairing machine. -/
lemma DeferralFunction.graphFlag_ruler (f : DeferralFunction) : UnaryRuler f.graphFlag := by
  obtain ⟨G, hG, hGeq⟩ := f.graph_fp
  have h := Complexity.mem_FP_comp Complexity.unaryLength_mem_FP hG
  show (fun z : List Bool => List.replicate (f.graphFlag z.length) false) ∈ Complexity.FP
  have heq : (G ∘ fun z : List Bool => List.replicate z.length true)
      = fun z : List Bool => List.replicate (f.graphFlag z.length) false := by
    funext z
    simp only [Function.comp_apply]
    have hz := hGeq z.length.unpair.1 z.length.unpair.2
    rw [Nat.pair_unpair] at hz
    rw [hz]
    rfl
  rwa [heq] at h

/-- **Non-vacuity of `def:deferralfunc`** — kind `N+` non-vacuity witness.  The successor
`n ↦ n + 1` is a deferral function: it defers (`n < n + 1`), and its graph `n + 1 = m` is one
length comparison on the unary pair, so the machine decides it in polynomial time.  Every
`DeferralFunction` binder in this file and in the `thm:cee` / `thm:ceu` / `thm:ccee` /
`thm:st` endpoints is therefore inhabited.

This witness is **slow-growing**, so on its own it exercises none of the reason condition 2
is stated output-sensitively; `doublingDeferral` below is the fast-growing companion.
Provenance: (a) derived in-project. -/
def succDeferral : DeferralFunction where
  f := (· + 1)
  lt n := Nat.lt_succ_self n
  graph_fp :=
    ⟨fun z : List Bool =>
        List.replicate (if z.length.unpair.1 + 1 = z.length.unpair.2 then 1 else 0) false,
      UnaryRuler.eqFlag UnaryRuler.unpairFst.succ UnaryRuler.unpairSnd,
      fun n m => by simp⟩

/-- **A fast-growing deferral function** — kind `N+` non-vacuity witness, and the one that
exercises why `def:deferralfunc`'s efficiency clause is stated output-sensitively.  `n ↦ 2 ^ n`
defers (`n < 2 ^ n`), and its graph is decided in polynomial time on the unary pair because
the *capped* power is: `2 ^ n = m` exactly when `min (2 ^ n) (m + 1) = m`, and
`UnaryRuler.two_pow_min` computes that cap as a doubling loop truncated at `m + 1` every
step, so the loop's state never exceeds the input's own length.  The uncapped `2 ^ n` is not
a ruler and could not be — its word would be exponentially long — which is exactly why the
clause is read on the pair rather than on `n` alone.
Provenance: (a) derived in-project. -/
def doublingDeferral : DeferralFunction where
  f n := 2 ^ n
  lt _ := Nat.lt_two_pow_self
  graph_fp :=
    ⟨fun z : List Bool =>
        List.replicate (if min (2 ^ z.length.unpair.1) (z.length.unpair.2 + 1)
          = z.length.unpair.2 then 1 else 0) false,
      UnaryRuler.eqFlag
        (UnaryRuler.two_pow_min UnaryRuler.unpairFst UnaryRuler.unpairSnd.succ
          (fun _ => Nat.succ_pos _))
        UnaryRuler.unpairSnd,
      fun n m => by
        simp only [List.length_replicate, Nat.unpair_pair]
        have hiff : (min (2 ^ n) (m + 1) = m) ↔ (2 ^ n = m) := by omega
        simp only [hiff]⟩

/-- **No whole-value fuel clock certifies `doublingDeferral`.**  `not_polyFueled_two_pow`
refutes a `PolyFueled` certificate for `n ↦ 2 ^ n` on output size alone — the class bounds
the value returned by a polynomial in the input, and `2 ^ n` is not so bounded.  So the
fast-growing regime that `DeferralFunction.graph_fp` admits is *not* reachable by a
fuel-clocked reading of the same clause, and the machine reading is doing real work here
rather than restating a fuel condition under another name.  This is a size-based separation
only; no time lower bound is claimed.
Provenance: (b) `not_polyFueled_two_pow`. -/
lemma not_polyFueled_doublingDeferral (c : Nat.Partrec.Code) :
    ¬ PolyFueled c doublingDeferral.f :=
  not_polyFueled_two_pow c

/-! ## The day-bounded deferral schedule

The graph test is polynomial in the pair `⟨k, m⟩`, so on day `n` a machine can scan
`m = 0, …, n` and report `f k` exactly when the deferral deadline has already fallen — and
cannot learn it otherwise, `f k` being potentially far beyond the day's budget.
`scheduledValue` is that day-bounded lookup, `scheduledMatch` the day-indexed flag that is
`1` exactly when component `k` defers to the current day, and `deadlineRun` the same lookup
in the normalized `0`/`f k + 1` shape the settlement clock tests.

All three are stated here, beside `DeferralFunction` itself, because both
`Construction/Statistics/` and `Construction/Quotation/` consume them; putting them in
either lane would make that pair of lanes import each other. -/

/-- The day-bounded deferral lookup at `⟨day, component⟩`: `f k` once day `n` has reached
it, `0` before.  The scan is the prefix sum of `m ↦ m * ⟦f k = m⟧` over `m ≤ n`, which picks
out the one matching value. -/
def scheduledValue (f : DeferralFunction) (z : ℕ) : ℕ :=
  segPrefix (fun w => w.unpair.2 * f.graphFlag w) z.unpair.2 (z.unpair.1 + 1)

/-- The scan is the matching value once it has been passed, and `0` before. -/
private lemma scheduledScan (f : DeferralFunction) (k : ℕ) : ∀ r : ℕ,
    segPrefix (fun w => w.unpair.2 * f.graphFlag w) k r = if f.f k < r then f.f k else 0
  | 0 => by simp
  | r + 1 => by
      rw [segPrefix_succ, scheduledScan f k r]
      simp only [DeferralFunction.graphFlag, Nat.unpair_pair]
      by_cases h : f.f k = r
      · subst h
        simp
      · simp only [h, if_false, Nat.mul_zero, Nat.add_zero]
        split_ifs <;> omega

/-- The closed form of the day-bounded lookup. -/
lemma scheduledValue_eq_ite (f : DeferralFunction) (z : ℕ) :
    scheduledValue f z = if f.f z.unpair.2 ≤ z.unpair.1 then f.f z.unpair.2 else 0 := by
  rw [scheduledValue, scheduledScan]
  simp

/-- Once the runtime day has reached `f k`, the lookup has converged to the true deferral
value.  This is the fact every consumer of the schedule opens it by. -/
lemma scheduledValue_eq (f : DeferralFunction) {n k : ℕ} (hkn : f k ≤ n) :
    scheduledValue f (Nat.pair n k) = f k := by
  rw [scheduledValue_eq_ite]
  simp [hkn]

/-- The day-bounded lookup is machine-metered: polynomial time in the unary pair
`⟨day, component⟩`, whose length dominates the day. -/
lemma unaryRuler_scheduledValue (f : DeferralFunction) :
    UnaryRuler (scheduledValue f) :=
  ((UnaryRuler.segPrefix (UnaryRuler.unpairSnd.mul f.graphFlag_ruler)).comp
    (UnaryRuler.unpairSnd.pair UnaryRuler.unpairFst.succ)).of_eq
    (fun z => by simp [scheduledValue])

/-- `1` exactly when component `k` defers to the current day `n`.  The natural-valued flag
is the form consumed by the flat stream combinators. -/
def scheduledMatch (f : DeferralFunction) (z : ℕ) : ℕ :=
  if f z.unpair.2 = z.unpair.1 then 1 else 0

/-- The match flag is machine-metered: it is the graph test at the transposed pair. -/
lemma unaryRuler_scheduledMatch (f : DeferralFunction) :
    UnaryRuler (scheduledMatch f) :=
  (f.graphFlag_ruler.comp (UnaryRuler.unpairSnd.pair UnaryRuler.unpairFst)).of_eq
    (fun z => by simp [scheduledMatch, DeferralFunction.graphFlag])

/-- The match flag is Boolean. -/
lemma scheduledMatch_zero_or_one (f : DeferralFunction) (z : ℕ) :
    scheduledMatch f z = 0 ∨ scheduledMatch f z = 1 := by
  simp only [scheduledMatch]
  split <;> simp

/-- The match flag fires exactly on the deferral. -/
lemma scheduledMatch_eq_one_iff (f : DeferralFunction) (n k : ℕ) :
    scheduledMatch f (Nat.pair n k) = 1 ↔ f k = n := by
  simp [scheduledMatch]

/-- The match flag is `0` exactly when the component does not defer to this day. -/
lemma scheduledMatch_eq_zero_iff (f : DeferralFunction) (n k : ℕ) :
    scheduledMatch f (Nat.pair n k) = 0 ↔ f k ≠ n := by
  simp [scheduledMatch]

/-- The day-bounded lookup in the normalized shape the settlement clock tests: `0` while the
deadline has not fallen, else `f k + 1`. -/
def deadlineRun (f : DeferralFunction) (n k : ℕ) : ℕ :=
  if f k ≤ n then f k + 1 else 0

/-- The normalized lookup is machine-metered.  `f k ≥ 1`, so the lookup is `0` exactly when
the deadline has not fallen, and the sentinel is one `ifZero` on the lookup itself. -/
lemma unaryRuler_deadlineRun (f : DeferralFunction) :
    UnaryRuler (fun z => deadlineRun f z.unpair.1 z.unpair.2) := by
  have hval := unaryRuler_scheduledValue f
  refine (hval.add (hval.ifZero (UnaryRuler.const 0) (UnaryRuler.const 1))).of_eq
    (fun z => ?_)
  have hpos : 0 < f.f z.unpair.2 := Nat.lt_of_le_of_lt (Nat.zero_le _) (f.lt _)
  rw [scheduledValue_eq_ite, deadlineRun]
  split_ifs <;> omega

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
  source_codes : LUV.MachineThresholdCodeSeq X
  quote_codes : LUV.MachineThresholdCodeSeq Y
  reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    v.ValuesAt (Y n) ((X n).expect P (f n))
  affine : AffineQuoteEq P f (fun n => (X n).expect P n - (Y n).expect P n)

/-- Complete quote certificate for `thm:ceu`.
Paper node: `thm:ceu` -/
structure FuturePriceQuote (P : History) (DP : DeductiveProcess)
    (f : DeferralFunction) (φ : ℕ → Sentence) (Y : ℕ → LUV) where
  sentence_codes : MachineSentenceCodes φ
  quote_codes : LUV.MachineThresholdCodeSeq Y
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
`Construction/Quotation/MarketQuoteCodes.lean` is where this is worked out).
The general-source construction instead reads the deferred weight through its own
threshold atoms on a width-`n+1` mesh, which pins the product to within `1/(n+1)`.  The
exact-reflection case is the `slack = 0` instance and is still inhabited (the indicator
source), so this is a genuine weakening of the certificate, not a vacuous one.
Paper node: `thm:ccee` -/
structure ConditionalExpectationQuote (P : History) (DP : DeductiveProcess)
    (f : DeferralFunction) (X Z Z' : ℕ → LUV) (w : ℕ → ℚ) where
  weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1
  weight_generable : PGenerableRat P w
  source_codes : LUV.MachineThresholdCodeSeq X
  left_codes : LUV.MachineThresholdCodeSeq Z
  right_codes : LUV.MachineThresholdCodeSeq Z'
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
class: `PGenerableRat.ofMachineRatCodes` admits `p n = 1 − 2⁻ⁿ` and every other sequence
whose codes are exponential but polynomially writable (`pGenerableRat_two_pow_inv`).

Both quoted LUVs carry their threshold families in the **write-out** class
(`LUV.MachineThresholdCodeSeq`), the same meter `sentence_codes` uses and the one the rest of
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
  sentence_codes : MachineSentenceCodes φ
  probability_generable : PGenerableRat P p
  product_codes : LUV.MachineThresholdCodeSeq A
  confidence_codes : LUV.MachineThresholdCodeSeq B
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
      have hlo := AffineCombination.BoundedAffinePrices.futureLow_le_price
        q.bounded (f.lt n).le
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
      have hhi := AffineCombination.BoundedAffinePrices.price_le_futureHigh
        q.bounded (f.lt n).le
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
    have hhi := AffineCombination.BoundedAffinePrices.price_le_futureHigh
        q.bounded (f.lt n).le
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
