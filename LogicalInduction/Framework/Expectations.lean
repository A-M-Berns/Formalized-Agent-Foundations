import LogicalInduction.Framework.Emission.Computable
import LogicalInduction.Framework.Asymptotics
import LogicalInduction.Framework.Emission.RpnSplice
import LogicalInduction.Framework.Emission.WriteOut
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Expectations of LUVs (`def:luv`, `def:e`) and the ℙ̄-generable class (`def:ece`)

This module renders §4.8 `sec:expectations` (tex:1627) — `def:luv` (tex:1635) and `def:e`
(tex:1670) — together with the `def:ece` generability class (tex:1218) over which the affine
and self-trust results quantify.

* `GeneratedRatFeature` / `PGenerableRat` — `def:ece` for rational sequences, with the
  emission field write-out metered (`BigSpliceStream`), and the constructor
  `PGenerableRat.ofDigitRatCodes`. The width is load-bearing: `pGenerableRat_two_pow_inv`
  shows the paper's own `δ n = 2⁻ⁿ` is admitted here and refutes `PolyRatCodes`.
* `LUV` — a `[0,1]`-logically-uncertain variable presented by its threshold sentences
  `X.gt r = ⌜X > r⌝`, which is a LUV's entire observable content for a market. The paper's
  LUVs are *first-order* — a formula `X(ν)` free in one variable over a theory `Θ` that
  represents computations — and that literal object is `PaperLUV`
  (`Construction/LUV/PaperLUV.lean`), an actual one-variable arithmetic formula
  carrying object-level `T`-proofs, which compiles into this carrier. Results stated here
  are therefore stated of more families than the paper's, and `PaperLUV` is what shows the
  paper's own are among them. The paper's well-definedness (`Θ` proves a unique value)
  becomes monotonicity and coherence conditions on the threshold family, carried as the
  explicit hypotheses a given theorem needs rather than reconstructed as first-order syntax.
* The threshold-code interfaces, at three meters: whole-value (`LUV.PolyThresholdCodes`,
  `LUV.PolyThresholdCodeSeq`), token (`LUV.RpnThresholdCodes`, `LUV.RpnThresholdCodeSeq`)
  and write-out (`LUV.BigThresholdCodes`, `LUV.BigThresholdCodeSeq`), with the embeddings
  `ofPolyThresholdCodes` and `toBig`. `README.md` records which endpoints bind the token
  forms and why that is a rendering sensitivity rather than a narrowing of `def:ec`.
* `LUV.expectApprox` and `LUV.expect` — `def:e`'s finite price sum
  `𝔼_k^V(X) = (1/k) · ∑_{i<k} V(⌜X > i/k⌝)`, with the day-`n` operator taken at precision
  `n + 1` under the repo's day-index convention (Lean day `n` = paper day `n+1`,
  `Framework/Foundations.lean`), so every day has a nondegenerate grid and the grid error is
  `1/(n+1)`. `expectApprox_nonneg` and `expectApprox_le_one` inherit `[0,1]` from the prices.
* `PCWorld.ValuesAt` and `PCWorld.ApproxValuesUpTo` — the market-observable content of "`v`
  believes `X = x`", with `PCWorld.expectApprox_near_ofGrid` and
  `PCWorld.ValuesAt.expectApprox_near` the `lem:conluvapprox` counting argument (tex:4982)
  at the single-LUV form the affine results consume.
* `PCWorld.RationalCutAt` — the completed-world half of `def:luv` (tex:1635): a plausible
  world values an abstract `LUV` exactly when its true rational thresholds form a downward
  cut bounded into `[0,1]`. `carrier`, `carrier_nonempty` and `carrier_bddAbove` cut out the
  represented set of reals; `exists_valuesAt` turns a cut into a `PCWorld.ValuesAt` value,
  which is the world–value hypothesis every `lem:conluvapprox` consumer takes; and
  `valuesAt_iff_sSup` identifies that value canonically with `sSup (carrier v X)`, even
  though truth at a threshold equal to the value may remain undecided. The cut hypothesis is
  discharged for the paper's literal first-order LUVs by `PaperLUV.source_valued`
  (`Construction/LUV/PaperLUV.lean`) and in
  `Construction/SemanticExtension/Source.lean`. That section is presentation-free and
  certificate-free: no declaration in it mentions emission, fuel or source syntax, or takes
  a code or a fuel bound.
* `LUV.IsIndicator` — the relational rendering of the paper's `1(φ)`, quantified over
  completed-theory worlds (`PCWorld.ConsistentWithTheory`, the quantifier of `app:ei`'s own
  argument) rather than over every finite stage; `indicatorWitness_isIndicator` and
  `indicatorWitness_not_stagewise` show that the stage-quantified reading would exclude the
  paper's own indicator.

**Design.**  Paper-side LUV *constructions* — indicators, affine combinations — enter as
relational predicates over arbitrary threshold families, never as canonical `LUV` values; the
reason is given at `## Indicator families` below.

`thm:ec` itself is proved in `Properties/ExpectationConvergence.lean`
(`LUV.expect_converges`), which needs the completed-theory world-value linkage this module
does not carry.
-/

namespace LogicalInduction

open Filter Topology

/-! ## Efficient family interfaces (`def:ece`)

The paper's affine, Self-Trust, and introspection theorems quantify over efficiently
computable sequences.
An arbitrary Lean function `ℕ → Sentence` or `ℕ → LUV` is much broader: it can encode an
uncomputable diagonal that no legal trader can follow.  These interfaces expose exactly the
compact codes consumed by the token-emission model. -/

/-- A rational sequence generated continuously from the market by a polynomial-size,
closed feature progression. This is the propositional/token-model rendering of the
paper's `def:ece` for rational sequences. Closure is load-bearing: internal `EF.var`
nodes are legal only underneath the shared `letE` emitter and cannot be free inputs.

The emission field is **write-out metered** (`BigSpliceStream`): the feature progression
costs polynomially many *symbols* per day, with no bound on any single token's numeric
value. That is what admits a constant leaf `EF.const (q n)` whose payload token is
literally `⌜q n⌝` — for the paper's own `δ n = 2⁻ⁿ` an exponential value, and so outside
the value-metered `RpnSpliceStream` (`digitRatCodes_two_pow_inv_not_polyRatCodes`).
`PGenerableRat.ofDigitRatCodes` is the constructor that uses the width;
`pGenerableRat_two_pow_inv` is the witness that it is a real one.
Paper node: `def:ece` -/
structure GeneratedRatFeature (P : History) (q : ℕ → ℚ)
    (feature : ℕ → EF) : Prop where
  rank_le : ∀ n, (feature n).rank ≤ n
  polyTok : BigSpliceStream (fun n => (feature n).serialize)
  closed : ∀ n ρ V, (feature n).denoteWith ρ V = (feature n).denote V
  denote : ∀ n, (feature n).denote P = (q n : ℝ)

/-- **ℙ̄-generability for rational sequences** — the paper's `def:ece` (tex:1218) at the
rational case: `q` is generable from the market `P` when some efficiently computable feature
progression denotes it day by day. `GeneratedRatFeature` is the certificate this existential
ranges over, and `PGenerableRat.ofDigitRatCodes` is the constructor that produces one from
digit access to `q`. -/
def PGenerableRat (P : History) (q : ℕ → ℚ) : Prop :=
  ∃ feature : ℕ → EF, GeneratedRatFeature P q feature

/-- A rational sequence viewed as a closed constant feature on each day. -/
def ratCodeFeature (q : ℕ → ℚ) (n : ℕ) : EF :=
  EF.const (q n)

/-- **The write-out constructor for `def:ece`.**  A rational sequence whose numerator and
denominator are reachable digit by digit generates itself at any market, through
`ratCodeFeature`: the day-`n` serialization is the single payload chunk `[1, ⌜q n⌝]`,
emitted by `BigSpliceStream.serialize_const_write`, whose payload token is written out
digit by digit and so may be exponential in `n`.
Kind: `P` proved; provenance: (a) derived in-project. -/
lemma ratCodeFeature_generated (P : History) (q : ℕ → ℚ) (hq : DigitRatCodes q) :
    GeneratedRatFeature P q (ratCodeFeature q) where
  rank_le := fun n => by simp [ratCodeFeature, EF.rank]
  polyTok := BigSpliceStream.serialize_const_write hq.toBigDigits
  closed := fun n ρ V => by simp [ratCodeFeature]
  denote := fun n => by simp [ratCodeFeature]

/-- **The write-out constructor for `def:ece`.**  Digit access to a rational sequence makes
it ℙ‾-generable at any market.

This is the general constructor; `PGenerableRat.ofPolyRatCodes`
(`Construction/Quotation/ProductDefinition.lean`) is the value-bounded corollary, kept only
for callers already holding a `PolyRatCodes` certificate.  The width is not cosmetic: the
paper's `δ n = 2⁻ⁿ` satisfies this and refutes `PolyRatCodes`
(`digitRatCodes_two_pow_inv_not_polyRatCodes`).
Kind: `C` composition; provenance: (a) derived in-project. -/
lemma PGenerableRat.ofDigitRatCodes {q : ℕ → ℚ} (hq : DigitRatCodes q) (P : History) :
    PGenerableRat P q :=
  ⟨ratCodeFeature q, ratCodeFeature_generated P q hq⟩

/-- **Non-vacuity for the widened `def:ece` (kind `N+`).**  The paper's own tolerance
sequence `δ n = 2⁻ⁿ` is ℙ‾-generable at every market, and its Gödel codes are *not*
value-bounded — so this witness is admitted by `PGenerableRat.ofDigitRatCodes` and by no
route through `PGenerableRat.ofPolyRatCodes`.  It is the concrete content of widening
`GeneratedRatFeature.polyTok` from `RpnSpliceStream` to `BigSpliceStream`. -/
lemma pGenerableRat_two_pow_inv (P : History) :
    PGenerableRat P (fun n => (((2 ^ n : ℕ) : ℚ))⁻¹) ∧
      ¬ PolyRatCodes (fun n => (((2 ^ n : ℕ) : ℚ))⁻¹) :=
  ⟨PGenerableRat.ofDigitRatCodes digitRatCodes_two_pow_inv P,
    digitRatCodes_two_pow_inv_not_polyRatCodes.2⟩

/-! ## Logically uncertain variables (`def:luv`) -/

/-- `def:luv` (abstracted). A `[0,1]`-logically-uncertain variable, presented by its
threshold sentences: `X.gt r = ⌜X > r⌝`. This is the LUV's entire observable content for a
market, which prices those sentences.
Paper node: `def:luv` -/
structure LUV where
  /-- The sentence `⌜X > r⌝`, for a rational threshold `r`. -/
  gt : ℚ → Sentence

/-- LUVs are determined by their threshold-sentence families. -/
@[ext] protected lemma LUV.ext {X Y : LUV} (h : X.gt = Y.gt) : X = Y := by
  cases X
  cases Y
  cases h
  rfl

namespace LUV

/-! ## Threshold-code interfaces (`def:ec`) -/

/-- A threshold presentation is **polynomially codeable** when the sentence code for
`X > i/n` is computable with polynomial fuel from `⟨n,i⟩`.  Paper LUVs are
Θ-definable, so this is the propositional interface corresponding to their compact
syntactic presentation (`def:ec`, disclosed type-`(c)`). -/
def PolyThresholdCodes (X : LUV) : Prop :=
  ∃ c : Nat.Partrec.Code, PolyFueled c (fun m =>
    Encodable.encode (X.gt ((m.unpair.2 : ℚ) / (m.unpair.1 : ℚ))))

/-- A sequence of LUV presentations is polynomially codeable when `⌜X_n > i/k⌝` can be
emitted from `⟨n,⟨k,i⟩⟩`. This is the varying-LUV analogue of `PolyThresholdCodes` and is
the interface needed by the affine and Self-Trust traders. -/
def PolyThresholdCodeSeq (X : ℕ → LUV) : Prop :=
  ∃ c : Nat.Partrec.Code, PolyFueled c (fun m =>
    Encodable.encode ((X m.unpair.1).gt
      ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ))))

/-! ### Block form of the threshold interfaces (`def:ec`)

`PolyThresholdCodes` meters the *pair code* of the threshold sentence, which excludes deep
or skewed threshold families whose codes are value-exponential in their symbol count. The
faithful `def:ec` reading meters **symbols**: a `PolySegStream` of self-delimiting sentence
blocks parsing to the thresholds, at the same paired-index convention. These are the block
forms; the whole-value interfaces embed into them by `ofPolyThresholdCodes`. -/

/-- Block form of `PolyThresholdCodes`: an 𝓔𝓒 sentence-block stream emitting `⌜X > i/k⌝`
at index `⟨k,i⟩`. Paper node: `def:ec` -/
def RpnThresholdCodes (X : LUV) : Prop :=
  RpnSentenceCodes (fun m => X.gt ((m.unpair.2 : ℚ) / (m.unpair.1 : ℚ)))

/-- Block form of `PolyThresholdCodeSeq`: an 𝓔𝓒 sentence-block stream emitting
`⌜X_n > i/k⌝` at index `⟨n,⟨k,i⟩⟩`. Paper node: `def:ec` -/
def RpnThresholdCodeSeq (X : ℕ → LUV) : Prop :=
  RpnSentenceCodes (fun m => (X m.unpair.1).gt
    ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ)))

/-- **Write-out form** of the single-LUV threshold interface: a `def:ec` *write-out* sentence
stream emitting `⌜X > i/k⌝` at index `⟨k,i⟩`, at exactly the paired-index convention of
`RpnThresholdCodes`.  It is the single-LUV analogue of `BigThresholdCodeSeq`, and stands to
`RpnThresholdCodes` as that class stands to `RpnThresholdCodeSeq`: the two differ only in the
meter on the underlying sentence stream, `RpnThresholdCodes` bounding every emitted token's
*value* and this one only their number. -/
def BigThresholdCodes (X : LUV) : Prop :=
  BigSentenceCodes (fun m => X.gt ((m.unpair.2 : ℚ) / (m.unpair.1 : ℚ)))

/-- **Write-out form** of the threshold sequence interface: a `def:ec` *write-out* sentence
stream emitting `⌜X_n > i/k⌝` at index `⟨n,⟨k,i⟩⟩`, at exactly the paired-index convention
of `RpnThresholdCodeSeq`.  The two differ only in the meter on the underlying sentence
stream — `RpnThresholdCodeSeq` bounds every emitted *token's value*, this one bounds only
the number of tokens — so this is the class the paper's `def:ec` actually names, and it is
where the rest of the day-indexed surface sits.
Paper node: `def:ec` -/
def BigThresholdCodeSeq (X : ℕ → LUV) : Prop :=
  BigSentenceCodes (fun m => (X m.unpair.1).gt
    ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ)))

/-- The token-metered single-LUV threshold interface embeds into the write-out one. -/
lemma RpnThresholdCodes.toBig {X : LUV}
    (h : X.RpnThresholdCodes) : X.BigThresholdCodes :=
  BigSentenceCodes.ofRpnSentenceCodes h

/-- The token-metered threshold sequence interface embeds into the write-out one. -/
lemma RpnThresholdCodeSeq.toBig {X : ℕ → LUV}
    (h : RpnThresholdCodeSeq X) : BigThresholdCodeSeq X :=
  BigSentenceCodes.ofRpnSentenceCodes h

/-- The whole-value threshold interface embeds into the block form by escape blocks. -/
lemma RpnThresholdCodes.ofPolyThresholdCodes {X : LUV} (h : X.PolyThresholdCodes) :
    X.RpnThresholdCodes :=
  RpnSentenceCodes.ofPolySentenceCodes h

/-- The whole-value sequence interface embeds into the block form by escape blocks. -/
lemma RpnThresholdCodeSeq.ofPolyThresholdCodeSeq {X : ℕ → LUV}
    (h : PolyThresholdCodeSeq X) : RpnThresholdCodeSeq X :=
  RpnSentenceCodes.ofPolySentenceCodes h

/-! ## Expectations (`def:e`) -/

/-- `def:e`. The **approximate expectation** of `X` under a valuation `V` at precision `k`:
`𝔼_k^V(X) = ∑_{i<k} (1/k) · V(⌜X > i/k⌝)`. Lands in `[0,1]` when `V` does (a share is worth
at most 1), so expectations of `[0,1]`-LUVs are themselves `[0,1]`-valued. -/
noncomputable def expectApprox (V : Valuation) (k : ℕ) (X : LUV) : ℝ :=
  (k : ℝ)⁻¹ * ∑ i ∈ Finset.range k, V (X.gt ((i : ℚ) / (k : ℚ)))

/-- `𝔼ₙ := 𝔼_n^{Pₙ}` — the day-`n` expectation, precision tied to the day (`def:e`).

Under the repo's day-index convention (Lean day `n` = paper day `n+1`, see
`Framework/Foundations.lean`), the paper's precision-and-day pairing is `n + 1` on both
sides: Lean day `n` carries the paper's precision-`n+1` operator `𝔼_{n+1}^{P_{n+1}}`. In
particular every day — day `0` included — has a nondegenerate grid, and the `1/k` grid
error bounds are `1/(n+1)`, whose positivity is free. -/
noncomputable def expect (P : History) (n : ℕ) (X : LUV) : ℝ :=
  X.expectApprox (P n) (n + 1)

/-- The **expectation sequence** `n ↦ 𝔼ₙ(X)` derived from the market `P`: the `ℕ → ℝ`
sequence of day-`n` expectations of `X`. Limit statements about it are phrased in the shared
asymptotic vocabulary of `Framework/Asymptotics` (`≈ₙ`, `≳ₙ`, `≲ₙ`, convergence; `dd:asymp`),
which is where that vocabulary is defined once for the whole development. -/
noncomputable def expectSeq (P : History) (X : LUV) : ℕ → ℝ := fun n => X.expect P n

/-! ## Basic bounds — `𝔼` inherits `[0,1]` from the prices. -/

lemma expectApprox_nonneg (V : Valuation) (k : ℕ) (X : LUV)
    (hV : ∀ s, 0 ≤ V s) : 0 ≤ X.expectApprox V k := by
  refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => hV _))

lemma expectApprox_le_one (V : Valuation) (k : ℕ) (X : LUV)
    (hV : ∀ s, V s ≤ 1) : X.expectApprox V k ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · simp [expectApprox, hk]
  · have hsum : ∑ i ∈ Finset.range k, V (X.gt ((i : ℚ) / (k : ℚ))) ≤ (k : ℝ) := by
      calc ∑ i ∈ Finset.range k, V (X.gt ((i : ℚ) / (k : ℚ)))
          ≤ ∑ _i ∈ Finset.range k, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hV _)
        _ = k := by simp
    rw [expectApprox, inv_mul_le_iff₀ (by exact_mod_cast hk)]
    simpa using hsum

lemma expect_mem_Icc (P : History) (n : ℕ) (X : LUV)
    (hP : ∀ s, 0 ≤ P n s ∧ P n s ≤ 1) : 0 ≤ X.expect P n ∧ X.expect P n ≤ 1 :=
  ⟨X.expectApprox_nonneg (P n) (n + 1) (fun s => (hP s).1),
   X.expectApprox_le_one (P n) (n + 1) (fun s => (hP s).2)⟩

/-! ## `thm:ec` — Expectations Converge

Proved in `Properties/ExpectationConvergence.lean` (`LUV.expect_converges`): the day-`n`
expectation is the price of the precision-`n+1` threshold bundle, so `thm:affcoh` traps it
between the limiting belief's liminf/limsup, and `thm:lc` averages the limiting belief
over completed-theory worlds, where `lem:conluvapprox` makes the precision sequence
Cauchy. The statement lives there (it needs the completed-theory world-value linkage `hval`,
quantified over `cworlds(Θ)`, and daily plausible worlds, on top of the price bounds). -/

end LUV

/-! ## World-side LUV values (`lem:conluvapprox`)

The paper's "`Θ` represents computations, so every consistent world assigns each LUV its
true value" becomes, in our threshold presentation, a coherence condition relating a world
to a value: `v` affirms every threshold strictly below `x` and denies every one strictly
above. This is the market-observable content of "`v` believes `X = x`" rather than a
first-order reconstruction — the literal reconstruction is `PaperLUV`, which derives its
world-value semantics instead of assuming it. -/

/-- The p.c. world `v` **values** the `[0,1]`-LUV `X` at `x`: threshold coherence around
`x`. -/
def PCWorld.ValuesAt (v : PCWorld) (X : LUV) (x : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ 1 ∧
    ∀ r : ℚ, ((r : ℝ) < x → v.Holds (X.gt r)) ∧ (x < (r : ℝ) → ¬ v.Holds (X.gt r))

/-- A world values a LUV at most one real: distinct candidates are separated by a rational
threshold the world would have to both affirm and deny.
Paper node: `def:luv` -/
lemma PCWorld.ValuesAt.eq {v : PCWorld} {X : LUV} {x y : ℝ}
    (hx : v.ValuesAt X x) (hy : v.ValuesAt X y) : x = y := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn h
    exact (hx.2.2 r).2 hr1 ((hy.2.2 r).1 hr2)
  · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn h
    exact (hy.2.2 r).2 hr1 ((hx.2.2 r).1 hr2)

/-- **`lem:conluvapprox`, single-LUV form at grid coherence** (tex:4982): a world that
values `X` at `x` assesses the precision-`n` approximate expectation within `1/n` of `x`.

Counting argument: thresholds `i/n` strictly below `x` pay `1` (there are at least
`⌈nx⌉ ≥ nx` of them among `i < n`, since `x ≤ 1`), thresholds strictly above pay `0`
(so the payout sum is at most `⌊nx⌋ + 1 ≤ nx + 1` — only `i ≤ ⌊nx⌋` can pay), and the
one possible threshold *equal* to `x` is the `+1` slack. Hence
`x ≤ 𝔼ₙ ≤ x + 1/n` — one-sided, which `|·|` weakens. Only this single-LUV form is needed:
the affine results in `Properties/ExpectationAffine.lean` combine per-LUV bounds rather
than a combination (`b/n`) form.

This result is deliberately carried without a `Paper node` line: `lem:conluvapprox` is
listed in `UNANNOTATED_PAPER_RESULTS` in `scripts/check_endpoint_coverage.py` against
`Properties/ExpectationConvergence.lean`. Do not add the annotation — it would put the
label under the per-declaration axiom gate, which this statement does not answer to. -/
theorem PCWorld.expectApprox_near_ofGrid {v : PCWorld} {X : LUV} {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {n : ℕ} (hn : 0 < n)
    (hgrid : ∀ i : ℕ, i < n →
      (((i : ℝ) / n < x → v.Holds (X.gt ((i : ℚ) / (n : ℚ)))) ∧
        (x < (i : ℝ) / n → ¬ v.Holds (X.gt ((i : ℚ) / (n : ℚ)))))) :
    |X.expectApprox v.payout n - x| ≤ 1 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcast : ∀ i : ℕ, (((i : ℚ) / (n : ℚ) : ℚ) : ℝ) = (i : ℝ) / (n : ℝ) := by
    intro i; push_cast; ring
  have hmem : ∀ i : ℕ, 0 ≤ v.payout (X.gt ((i : ℚ) / (n : ℚ)))
      ∧ v.payout (X.gt ((i : ℚ) / (n : ℚ))) ≤ 1 := by
    intro i; rw [PCWorld.payout]; split <;> norm_num
  have hone : ∀ i : ℕ, i < n → (i : ℝ) / n < x → v.payout (X.gt ((i : ℚ) / (n : ℚ))) = 1 := by
    intro i hin hi
    have h := (hgrid i hin).1 hi
    rw [PCWorld.payout, if_pos h]
  have hzero : ∀ i : ℕ, i < n → x < (i : ℝ) / n → v.payout (X.gt ((i : ℚ) / (n : ℚ))) = 0 := by
    intro i hin hi
    have h := (hgrid i hin).2 hi
    rw [PCWorld.payout, if_neg h]
  -- Lower bound: the first `min n ⌈nx⌉` thresholds all pay 1, and `min n ⌈nx⌉ ≥ nx`.
  have hsum_lo : (n : ℝ) * x
      ≤ ∑ i ∈ Finset.range n, v.payout (X.gt ((i : ℚ) / (n : ℚ))) := by
    calc (n : ℝ) * x ≤ (min n ⌈(n : ℝ) * x⌉₊ : ℕ) := by
          rcases le_total (⌈(n : ℝ) * x⌉₊) n with h | h
          · rw [min_eq_right h]
            exact_mod_cast Nat.le_ceil _
          · rw [min_eq_left h]
            nlinarith
      _ = ∑ i ∈ Finset.range (min n ⌈(n : ℝ) * x⌉₊),
            v.payout (X.gt ((i : ℚ) / (n : ℚ))) := by
          rw [Finset.sum_congr rfl (fun i hi => ?_), Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, mul_one]
          rw [Finset.mem_range] at hi
          have hin : i < n := lt_of_lt_of_le hi (min_le_left _ _)
          refine hone i hin ?_
          have hic : (i : ℝ) < (n : ℝ) * x :=
            Nat.lt_ceil.mp (lt_of_lt_of_le hi (min_le_right _ _))
          rw [div_lt_iff₀ hnR]
          linarith
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (min_le_left _ _)) (fun i _ _ => (hmem i).1)
  -- Upper bound: only thresholds with `i ≤ ⌊nx⌋` can pay, so the sum is `≤ ⌊nx⌋ + 1`.
  have hsum_hi : ∑ i ∈ Finset.range n, v.payout (X.gt ((i : ℚ) / (n : ℚ)))
      ≤ (n : ℝ) * x + 1 := by
    set c' := min n (⌊(n : ℝ) * x⌋₊ + 1) with hc'
    have hc'n : c' ≤ n := min_le_left _ _
    have hsplit := Finset.sum_range_add_sum_Ico
      (fun i => v.payout (X.gt ((i : ℚ) / (n : ℚ)))) hc'n
    have hpart1 : ∑ i ∈ Finset.range c', v.payout (X.gt ((i : ℚ) / (n : ℚ)))
        ≤ (c' : ℝ) := by
      calc ∑ i ∈ Finset.range c', v.payout (X.gt ((i : ℚ) / (n : ℚ)))
          ≤ ∑ _i ∈ Finset.range c', (1 : ℝ) :=
            Finset.sum_le_sum (fun i _ => (hmem i).2)
        _ = c' := by simp
    have hpart2 : ∑ i ∈ Finset.Ico c' n, v.payout (X.gt ((i : ℚ) / (n : ℚ))) = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      rw [Finset.mem_Ico] at hi
      obtain ⟨hi1, hi2⟩ := hi
      have hiM : ⌊(n : ℝ) * x⌋₊ + 1 ≤ i := by
        rcases le_total (⌊(n : ℝ) * x⌋₊ + 1) n with h | h
        · rwa [hc', min_eq_right h] at hi1
        · rw [hc', min_eq_left h] at hi1
          omega
      refine hzero i hi2 ?_
      have h1 : (n : ℝ) * x < (⌊(n : ℝ) * x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : ((⌊(n : ℝ) * x⌋₊ : ℝ) + 1) ≤ (i : ℝ) := by exact_mod_cast hiM
      rw [lt_div_iff₀ hnR]
      linarith
    have hc'M : (c' : ℝ) ≤ (⌊(n : ℝ) * x⌋₊ : ℝ) + 1 := by
      have h := min_le_right n (⌊(n : ℝ) * x⌋₊ + 1)
      exact_mod_cast h
    have hfl : ((⌊(n : ℝ) * x⌋₊ : ℝ)) ≤ (n : ℝ) * x :=
      Nat.floor_le (mul_nonneg hnR.le hx0)
    linarith
  -- Assemble: `x ≤ 𝔼 ≤ x + 1/n`.
  rw [LUV.expectApprox, abs_le]
  constructor
  · have hlo : x ≤ (n : ℝ)⁻¹
        * ∑ i ∈ Finset.range n, v.payout (X.gt ((i : ℚ) / (n : ℚ))) := by
      rw [le_inv_mul_iff₀ hnR]
      exact hsum_lo
    have h1n : (0 : ℝ) < 1 / n := by positivity
    linarith
  · have hhi : (n : ℝ)⁻¹
        * ∑ i ∈ Finset.range n, v.payout (X.gt ((i : ℚ) / (n : ℚ))) ≤ x + 1 / n := by
      rw [inv_mul_le_iff₀ hnR]
      calc ∑ i ∈ Finset.range n, v.payout (X.gt ((i : ℚ) / (n : ℚ)))
          ≤ (n : ℝ) * x + 1 := hsum_hi
        _ = (n : ℝ) * (x + 1 / n) := by field_simp
    linarith

/-- **`lem:conluvapprox`, single-LUV form.**  A world that values `X` at `x` assesses the
precision-`n` approximate expectation within `1/n` of `x` — the full-`ValuesAt` specialization of
`expectApprox_near_ofGrid` (the counting argument only ever needs grid-point coherence).

This result is deliberately carried without a `Paper node` line, for the reason spelled out
at `expectApprox_near_ofGrid` above. -/
theorem PCWorld.ValuesAt.expectApprox_near {v : PCWorld} {X : LUV} {x : ℝ}
    (hval : v.ValuesAt X x) {n : ℕ} (hn : 0 < n) :
    |X.expectApprox v.payout n - x| ≤ 1 / n := by
  obtain ⟨hx0, hx1, hthr⟩ := hval
  refine PCWorld.expectApprox_near_ofGrid hx0 hx1 hn (fun i _ => ?_)
  have hcast : (((i : ℚ) / (n : ℚ) : ℚ) : ℝ) = (i : ℝ) / (n : ℝ) := by push_cast; ring
  exact ⟨fun hi => (hthr ((i : ℚ) / (n : ℚ))).1 (by rw [hcast]; exact hi),
    fun hi => (hthr ((i : ℚ) / (n : ℚ))).2 (by rw [hcast]; exact hi)⟩

/-- Finite-precision world–value agreement up to precision `N`: the day-`n` approximate
expectation (for `0 < n ≤ N`) sits within `1/n` of `x`, with `x` nonneg.  Unlike the full
`PCWorld.ValuesAt` cut, this is realizable by a world that has only seen the grid thresholds up
to precision `N` — exactly what a finite deductive-process stage reveals.  It is the hypothesis
the expectation-convergence trader actually consumes (it uses `expectApprox_near` only at
precisions `≤ N`). -/
def PCWorld.ApproxValuesUpTo (v : PCWorld) (X : LUV) (x : ℝ) (N : ℕ) : Prop :=
  0 ≤ x ∧ ∀ n, 0 < n → n ≤ N → |X.expectApprox v.payout n - x| ≤ 1 / n

/-- Finite-precision agreement is downward closed in the precision. -/
lemma PCWorld.ApproxValuesUpTo.mono {v : PCWorld} {X : LUV} {x : ℝ} {M N : ℕ}
    (h : v.ApproxValuesUpTo X x N) (hMN : M ≤ N) : v.ApproxValuesUpTo X x M :=
  ⟨h.1, fun n hn hnM => h.2 n hn (hnM.trans hMN)⟩

/-- Full `ValuesAt` implies the finite-precision agreement at every `N`. -/
lemma PCWorld.ValuesAt.approxValuesUpTo {v : PCWorld} {X : LUV} {x : ℝ}
    (hx : v.ValuesAt X x) (N : ℕ) : v.ApproxValuesUpTo X x N :=
  ⟨hx.1, fun _ hn _ => hx.expectApprox_near hn⟩

/-! ## Indicator families

The definitions live here because expectation convergence consumes them, and keeping them
upstream of the affine layer avoids an import cycle. The theorems that use them —
`thm:ei`, `thm:loe`, `thm:expprovind` — are proved in `Properties/ExpectationAffine.lean`,
where the affine machinery is available.
**General principle:** paper-side LUV *constructions* — indicators, affine
combinations — enter our modeling as **relational predicates over arbitrary threshold
families**, never as canonical `LUV` values. Constructing a representative (e.g. defining
the indicator of `φ` as `gt r := φ` on `[0,1)`) would make the theorem *definitional* —
the collapse is a modeling artifact, since the paper's thresholds are distinct sentences
provably linked to `φ`, and the theorem's content is the inductor learning that growing
bundle of equivalences uniformly. -/

/-- `Y` is an **indicator family for `φ`** (relational rendering of the paper's `1(φ)`):
in every **completed-theory** world — `v ∈ cworlds(Θ)`, the exact quantifier of the paper's
`app:ei` argument — `Y`'s thresholds below `0` hold, thresholds in `[0,1)` are equivalent
to `φ`, and thresholds at `≥ 1` fail.

The quantifier is over `PCWorld.ConsistentWithTheory`, *not* over every finite stage
`DP.D n`.  Requiring the equivalences already in `pcworlds(D n)` for every `n` — stage `0`
included — would exclude the paper's own `1(φ)`: `Θ`'s threshold equivalences only enter
`D n` at some finite stage, so a process whose early stages are small has plausible day-`0`
worlds that break them.  `indicatorWitness_isIndicator` below exhibits exactly such a
`Y`/`φ`/`DP`. -/
def LUV.IsIndicator (Y : LUV) (φ : Sentence) (DP : DeductiveProcess) : Prop :=
  ∀ v : PCWorld, v.ConsistentWithTheory DP → ∀ r : ℚ,
    ((r : ℝ) < 0 → v.Holds (Y.gt r)) ∧
    (0 ≤ (r : ℝ) → (r : ℝ) < 1 → (v.Holds (Y.gt r) ↔ v.Holds φ)) ∧
    (1 ≤ (r : ℝ) → ¬ v.Holds (Y.gt r))

/-- The relational indicator hypotheses really assign the indicator its intended world value:
`1` in `φ`-worlds and `0` otherwise. This is the world-side input to `thm:ei` in
`Properties/ExpectationAffine.lean`. -/
lemma LUV.IsIndicator.valuesAt {Y : LUV} {φ : Sentence} {DP : DeductiveProcess}
    (hY : Y.IsIndicator φ DP) {v : PCWorld}
    (hv : v.ConsistentWithTheory DP) : v.ValuesAt Y (v.payout φ) := by
  have hlink := hY v hv
  by_cases hφ : v.Holds φ
  · rw [PCWorld.payout, if_pos hφ]
    refine ⟨by norm_num, by norm_num, fun r => ?_⟩
    obtain ⟨hneg, hmid, hhi⟩ := hlink r
    constructor
    · intro hr
      by_cases hr0 : (r : ℝ) < 0
      · exact hneg hr0
      · exact (hmid (le_of_not_gt hr0) hr).2 hφ
    · intro hr
      exact hhi (le_of_lt hr)
  · rw [PCWorld.payout, if_neg hφ]
    refine ⟨by norm_num, by norm_num, fun r => ?_⟩
    obtain ⟨hneg, hmid, hhi⟩ := hlink r
    constructor
    · exact hneg
    · intro hr
      by_cases hr1 : (r : ℝ) < 1
      · exact fun h => hφ ((hmid (le_of_lt hr) hr1).1 h)
      · exact hhi (le_of_not_gt hr1)

/-! ### Non-vacuity of `LUV.IsIndicator` (kind `N+`)

The class is inhabited by a *non-degenerate* indicator: thresholds that are not the
sentence `φ` itself, linked to it only by an equivalence the deductive process reveals.
This is the paper's `1(φ)` situation, and it is exactly what the stage-quantified reading
of `IsIndicator` excluded — the witness below fails the stage form at `n = 0` (`D 0` is
empty, so a day-`0` plausible world may set `atom 1` freely) while satisfying the
completed-theory form the paper's `app:ei` argument uses. -/

/-- The equivalence `atom 0 ↔ atom 1` the witness process reveals. -/
def indicatorWitnessLink : Sentence :=
  ((LO.Propositional.Formula.atom 0).imp (LO.Propositional.Formula.atom 1)).and
    ((LO.Propositional.Formula.atom 1).imp (LO.Propositional.Formula.atom 0))

/-- The revealing process for the indicator witness: from day `1` on, the theory asserts
`atom 0 ↔ atom 1`; day `0` asserts nothing. -/
def indicatorWitnessDP : DeductiveProcess where
  D := fun n => if n = 0 then ∅ else {indicatorWitnessLink}
  mono := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h1 : n ≠ 0 := by omega
      simp [h1]

/-- The witness LUV: thresholds below `0` are a tautology, thresholds in `[0,1)` are the
atom `1`, thresholds at `≥ 1` are `⊥`.  Note the thresholds mention `atom 1`, never the
indicated sentence `atom 0`. -/
def indicatorWitnessLUV : LUV where
  gt := fun r =>
    if r < 0 then (LO.Propositional.Formula.falsum).imp LO.Propositional.Formula.falsum
    else if r < 1 then LO.Propositional.Formula.atom 1
    else LO.Propositional.Formula.falsum

/-- **Non-vacuity for `LUV.IsIndicator` (kind `N+`).**  The witness really is an indicator
family for `atom 0` over `indicatorWitnessDP`, with thresholds distinct from the indicated
sentence. -/
lemma indicatorWitness_isIndicator :
    indicatorWitnessLUV.IsIndicator (LO.Propositional.Formula.atom 0) indicatorWitnessDP := by
  intro v hv r
  have hmem : indicatorWitnessLink ∈ indicatorWitnessDP.D 1 := by
    simp [indicatorWitnessDP]
  have hlink := hv 1 _ hmem
  simp only [indicatorWitnessLink, PCWorld.Holds,
    LO.Propositional.Formula.Boolean.val] at hlink
  have hiff : v.Holds (LO.Propositional.Formula.atom 1) ↔
      v.Holds (LO.Propositional.Formula.atom 0) := by
    simp only [PCWorld.Holds, LO.Propositional.Formula.Boolean.val] at hlink ⊢
    exact ⟨hlink.2, hlink.1⟩
  have hr0 : ((r : ℝ) < 0) ↔ r < 0 := by exact_mod_cast Iff.rfl
  have hr1 : ((r : ℝ) < 1) ↔ r < 1 := by exact_mod_cast Iff.rfl
  refine ⟨fun h => ?_, fun hlo hhi => ?_, fun h => ?_⟩
  · simp [indicatorWitnessLUV, hr0.mp h, PCWorld.Holds,
      LO.Propositional.Formula.Boolean.val]
  · have hnneg : ¬ (r < 0) := by
      intro hc; exact absurd (hr0.mpr hc) (not_lt.mpr hlo)
    simp only [indicatorWitnessLUV, if_neg hnneg, if_pos (hr1.mp hhi)]
    exact hiff
  · have hn1 : ¬ (r < 1) := fun hc => absurd (hr1.mpr hc) (not_lt.mpr h)
    have hn0 : ¬ (r < 0) := fun hc => hn1 (hc.trans (by norm_num))
    simp [indicatorWitnessLUV, if_neg hn0, if_neg hn1, PCWorld.Holds,
      LO.Propositional.Formula.Boolean.val]

/-- **The stage-quantified reading of `LUV.IsIndicator` is strictly too narrow.**  Demanding
the `[0,1)` equivalence already in `pcworlds(DP.D n)` for *every* `n` excludes
`indicatorWitnessLUV`, and hence the paper's own `1(φ)`: `indicatorWitnessDP.D 0` is empty, so
a day-`0` plausible world may set `atom 1` freely while `atom 0` fails.  This is the proved
obstruction that fixes `LUV.IsIndicator`'s quantifier at `PCWorld.ConsistentWithTheory`, and
it is recorded here — with no consumer, deliberately — so that the quantifier is not silently
re-tightened by a later reading of `app:ei`. -/
lemma indicatorWitness_not_stagewise :
    ¬ ∀ n (v : PCWorld), v.ConsistentWith (indicatorWitnessDP.D n) → ∀ r : ℚ,
      0 ≤ (r : ℝ) → (r : ℝ) < 1 →
        (v.Holds (indicatorWitnessLUV.gt r) ↔
          v.Holds (LO.Propositional.Formula.atom 0)) := by
  intro h
  have hv : (show PCWorld from fun i => i = 1).ConsistentWith (indicatorWitnessDP.D 0) := by
    simp [indicatorWitnessDP, PCWorld.ConsistentWith]
  have := h 0 _ hv 0 (by norm_num) (by norm_num)
  simp [indicatorWitnessLUV, PCWorld.Holds,
    LO.Propositional.Formula.Boolean.val] at this


section RationalCut

open Set

/-! ## The rational cut -/

/-- The completed-world content of a genuine paper `[0,1]` LUV (`def:luv`): the thresholds
`⌜X > r⌝` the world affirms form a downward cut of `ℚ` bounded into `[0,1]`. -/
structure PCWorld.RationalCutAt (v : PCWorld) (X : LUV) : Prop where
  /-- Every threshold below `0` holds. -/
  below_zero : ∀ r : ℚ, (r : ℝ) < 0 → v.Holds (X.gt r)
  /-- No threshold above `1` holds. -/
  above_one : ∀ r : ℚ, 1 < (r : ℝ) → ¬v.Holds (X.gt r)
  /-- Truth at a threshold is downward closed. -/
  downward : ∀ r s : ℚ, r < s → v.Holds (X.gt s) → v.Holds (X.gt r)

namespace PCWorld.RationalCutAt

variable {v : PCWorld} {X : LUV}

/-! ## The represented value -/

/-- The real set represented by the true rational thresholds of a cut. -/
def carrier (v : PCWorld) (X : LUV) : Set ℝ :=
  {x | ∃ r : ℚ, (r : ℝ) = x ∧ v.Holds (X.gt r)}

lemma carrier_nonempty (h : v.RationalCutAt X) : (carrier v X).Nonempty := by
  refine ⟨(-1 : ℝ), (-1 : ℚ), by norm_num, ?_⟩
  exact h.below_zero (-1) (by norm_num)

lemma carrier_bddAbove (h : v.RationalCutAt X) : BddAbove (carrier v X) := by
  refine ⟨1, ?_⟩
  rintro x ⟨r, rfl, hr⟩
  exact le_of_not_gt (fun hgt => h.above_one r hgt hr)

/-- A bounded downward rational cut determines a repository LUV value. -/
lemma exists_valuesAt (h : v.RationalCutAt X) : ∃ x : ℝ, v.ValuesAt X x := by
  let S := carrier v X
  have hSne : S.Nonempty := h.carrier_nonempty
  have hSbdd : BddAbove S := h.carrier_bddAbove
  refine ⟨sSup S, ?_, ?_, ?_⟩
  · by_contra hnonneg
    have hsupneg : sSup S < 0 := lt_of_not_ge hnonneg
    obtain ⟨r, hsup_r, hr0⟩ := exists_rat_btwn hsupneg
    have hrS : (r : ℝ) ∈ S := ⟨r, rfl, h.below_zero r hr0⟩
    exact (not_le_of_gt hsup_r) (le_csSup hSbdd hrS)
  · apply csSup_le hSne
    rintro x ⟨r, rfl, hr⟩
    exact le_of_not_gt (fun hgt => h.above_one r hgt hr)
  · intro r
    constructor
    · intro hr
      obtain ⟨y, ⟨s, hs, hsHolds⟩, hry⟩ := exists_lt_of_lt_csSup hSne hr
      subst y
      have hrs : r < s := by exact_mod_cast hry
      exact h.downward r s hrs hsHolds
    · intro hr hHolds
      have hrS : (r : ℝ) ∈ S := ⟨r, rfl, hHolds⟩
      exact (not_le_of_gt hr) (le_csSup hSbdd hrS)

/-- **Canonicity of the represented value**, the companion to `exists_valuesAt`: the value a
cut determines is not merely *some* real but exactly `sSup (carrier v X)`, and every
`PCWorld.ValuesAt` value of `X` at `v` is that supremum.  This holds even though truth at a
threshold equal to the value may remain undecided, so a client that has produced a value by
any other route may identify it with the supremum without re-deriving the cut. -/
lemma valuesAt_iff_sSup (h : v.RationalCutAt X) {x : ℝ} :
    v.ValuesAt X x ↔ x = sSup (carrier v X) := by
  have value_eq (z : ℝ) (hz : v.ValuesAt X z) : z = sSup (carrier v X) := by
    apply le_antisymm
    · by_contra hle
      obtain ⟨r, hsup_r, hrz⟩ := exists_rat_btwn (lt_of_not_ge hle)
      have hrHolds := (hz.2.2 r).1 hrz
      exact (not_le_of_gt hsup_r)
        (le_csSup h.carrier_bddAbove ⟨r, rfl, hrHolds⟩)
    · apply csSup_le h.carrier_nonempty
      rintro y ⟨r, rfl, hrHolds⟩
      exact le_of_not_gt (fun hzr => (hz.2.2 r).2 hzr hrHolds)
  constructor
  · exact value_eq x
  · intro hx
    obtain ⟨y, hy⟩ := h.exists_valuesAt
    rw [hx, ← value_eq y hy]
    exact hy

end PCWorld.RationalCutAt

end RationalCut
end LogicalInduction
