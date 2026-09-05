import LogicalInduction.Construction.Witnesses.PaperExactProduct
import LogicalInduction.Construction.Witnesses.PaperMarket
import LogicalInduction.Construction.Witnesses.PaperRepresentedWeight

/-!
# `thm:ccee` at zero slack, on the single market

This module renders `thm:ccee` (tex:2069) at zero slack, over the single paper-facing
market `liaHistory (paperDP T)`, for the paper's **literal** first-order LUV sources.

`lic_no_expected_net_update_conditional_closed` (`PaperMarket.lean`) states `thm:ccee` for
an **arbitrary** threshold-only source family, and pays for that generality with the
disclosed mesh slack (`dd:mesh`): nothing in the abstract `LUV` interface names a value, so
the quoted product can only be reconstructed from thresholds to within `1/(n+1)`.  For the
paper's literal first-order sources the product is exact, because arithmetic multiplies
pair codes exactly (`PaperExactProduct.lean`).  This module feeds that exact product into
the same generic trading argument at `slack = 0`.  The trade is exactness for generality,
and it is the only difference: same `paperDP T`, same market, same deductive process as
every other canonical endpoint.

Two declarations carry the content.
`lic_no_expected_net_update_conditional_paperLUV_ofWeightSeq` is parametric in the weight's
literal representation and holds the substance;
`lic_no_expected_net_update_conditional_paperLUV_closed` is the paper-facing endpoint,
which only supplies the represented weight `deferredWeightPaperLUVSeq`
(`PaperRepresentedWeight.lean`).  Its hypotheses are the paper's own, and are justified at
the declaration.

The two clients at the foot of the file are witnesses in the in-file style of
`ArithmeticSource.lean`: one varies the source over `𝗣𝗔` with deferral and weight left
hypothetical, the other discharges every binder.  `PaperLUVSeq` is not part of the curated
consumer import.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open Filter Topology

variable (T : ArithmeticTheory)

/-! ## The exact endpoint -/

/-- **`thm:ccee` at zero slack, parametric in the weight's literal representation.**  The
substance is here; the closed endpoint below only supplies the represented weight.
Kind `C`; hypotheses `(a)`.
Paper node: `thm:ccee` -/
lemma lic_no_expected_net_update_conditional_paperLUV_ofWeightSeq
    [T.Δ₁] [𝗜𝚺₁ ⪯ T] [Entailment.Consistent T]
    (f : DeferralFunction) (X W : PaperLUVSeq T)
    (w : ℕ → ℚ) (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat (liaHistory (paperDP T)) w)
    (weight_valued : ∀ n (v : PCWorld),
      v.ConsistentWithTheory (paperTheoryDP T) →
        v.ValuesAt (W.luv n).toLUV ((w (f n) : ℝ))) :
    (fun n ↦ ((paperExactProductLUVSeq X W).luv n).toLUV.expect
        (liaHistory (paperDP T)) n) ≈ₙ
      fun n ↦ ((paperConditionalExpectationQuoteCode T f (fun n => (X.luv n).toLUV)
        X.rpnThresholdCodeSeq w weight_generable weight_mem).luv n).expect
          (liaHistory (paperDP T)) n := by
  refine lic_no_expected_net_update_conditional_ofRepresentation_unconditional (T := T)
    f (fun n => (X.luv n).toLUV)
    (fun n => ((paperExactProductLUVSeq X W).luv n).toLUV)
    ((paperConditionalExpectationQuoteCode T f (fun n => (X.luv n).toLUV)
      X.rpnThresholdCodeSeq w weight_generable weight_mem).luv)
    w weight_mem weight_generable X.rpnThresholdCodeSeq
    (paperExactProductLUVSeq X W).rpnThresholdCodeSeq
    (paperConditionalExpectationQuoteCode T f (fun n => (X.luv n).toLUV)
      X.rpnThresholdCodeSeq w weight_generable weight_mem).poly
    (fun _ => 0) tendsto_const_nhds
    (fun n v hv => PaperLUV.source_valued (X.luv n) v
      (PCWorld.consistentWithTheory_union_right hv))
    (fun n v hv x hx => ⟨x * (w (f n) : ℝ), ?_, by simp⟩)
    (fun n v hv => ?_)
  · exact PaperLUV.paperProductPaperLUV_valuesAt (X.luv n) (W.luv n) v
      (PCWorld.consistentWithTheory_union_right hv) hx
      (weight_valued n v (PCWorld.consistentWithTheory_union_right hv))
  · have h := RationalQuoteCode.reflected (paperQuotationPresentation T)
      (paperConditionalExpectationQuoteCode T f (fun n => (X.luv n).toLUV)
        X.rpnThresholdCodeSeq w weight_generable weight_mem) n v hv
    rwa [Rat.cast_mul,
      ← (paperMarketComputation T).expectQuoteAt_cast
        (fun n => (X.luv n).toLUV) n (f.f n)] at h

/-- **`thm:ccee` (no expected net update under conditionals), closed form over the
constructed `LIA`, at zero slack, on the single market.**  The source is the paper's
*literal* first-order LUV family (`PaperLUVSeq`), the deferred weight is represented
literally inside `T` (`deferredWeightPaperLUVSeq`), and the left quoted product is their
**exact** arithmetic product — no mesh, no slack.  The market is
`liaHistory (paperDP T)`, the same one every other canonical endpoint names, and the
deductive process is the one fixed from `T` alone.

The general abstract-LUV form `lic_no_expected_net_update_conditional_closed` is the more
general-input result: it admits any threshold-only e.c. source, at the price of the
disclosed `dd:mesh` product slack.  This endpoint trades that
generality for exactness — literal first-order sources multiply exactly in arithmetic,
threshold-only ones do not.

`[RepresentsComputations T]` is the paper's own §2 premise on `Θ` (tex:606) and is what
represents the weight's numerator/denominator pair *function* inside `T` — its day-by-day
values, not any particular program for them: `RepresentsComputations.repr` is applied to
the function together with a `Computable` proof, and the resulting formula family depends
on the function's extension alone, so two different `PGenerableRat` certificates for the
same weight give literally the same formulas.  `weight_generable` is load-bearing through
the `Computable` proof it supplies, not as a choice of program.  The premise also supplies
consistency (`RepresentsComputations.consistent`).  `𝗣𝗔` instantiates every binder.

The weight is a `ℙ`-generable `ℚ`-sequence (`PGenerableRat`).  The paper writes `thm:ccee`'s
weight as a `ℙ`-generable sequence of *real* numbers in `[0,1]` (tex:2069), but at this
paper's markets that is the same class: a market prices into `ℚ ∩ [0,1]` (`def:marketprocess`)
and an expressible feature is built from price features, rational constants, `+`, `·`, `max`
and safe reciprocal (`def:tf`), so it evaluates to a rational; a `ℙ`-generable sequence, whose
`n`-th term *equals* such a feature's value (`def:ece`, not a limit of them), is therefore
rational-valued.  So `PGenerableRat` is coextensive with the paper's weight class here, not a
narrowing.
Kind `C`; hypotheses `(a)` — no modeling substitution.
Paper node: `thm:ccee` -/
theorem lic_no_expected_net_update_conditional_paperLUV_closed
    [T.Δ₁] [𝗜𝚺₁ ⪯ T] [RepresentsComputations T]
    (f : DeferralFunction) (X : PaperLUVSeq T)
    (w : ℕ → ℚ) (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat (liaHistory (paperDP T)) w) :
    (fun n ↦ ((paperExactProductLUVSeq X (deferredWeightPaperLUVSeq T
        (paperMarketComputation T) f w weight_generable weight_mem)).luv n).toLUV.expect
          (liaHistory (paperDP T)) n) ≈ₙ
      fun n ↦ ((paperConditionalExpectationQuoteCode T f (fun n => (X.luv n).toLUV)
        X.rpnThresholdCodeSeq w weight_generable weight_mem).luv n).expect
          (liaHistory (paperDP T)) n :=
  haveI := RepresentsComputations.consistent T
  lic_no_expected_net_update_conditional_paperLUV_ofWeightSeq T f X _ w weight_mem
    weight_generable
    (deferredWeightPaperLUVSeq_valuesAt T (paperMarketComputation T) f w
      weight_generable weight_mem)

/-! ## Clients of the exact same-market route

Two witnesses.  The first keeps the deferral and the weight hypothetical and varies only
the source: an actual, genuinely varying `PaperLUVSeq` — the paper's own `1/(n+1)`
family — goes through the endpoint over `𝗣𝗔`.  The second discharges **every** binder,
so the endpoint has a fully closed instance and no hypothesis of it is left unwitnessed.
Written in the in-file client style of `ArithmeticSource.lean`'s witnesses; `PaperLUVSeq`
is not part of the curated consumer import. -/

example (f : DeferralFunction) (w : ℕ → ℚ) (weight_mem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (weight_generable : PGenerableRat (liaHistory (paperDP 𝗣𝗔)) w) :
    (fun n ↦ ((paperExactProductLUVSeq (unitFracPaperLUVSeq 𝗣𝗔)
        (deferredWeightPaperLUVSeq 𝗣𝗔 (paperMarketComputation 𝗣𝗔) f w weight_generable
          weight_mem)).luv n).toLUV.expect (liaHistory (paperDP 𝗣𝗔)) n) ≈ₙ
      fun n ↦ ((paperConditionalExpectationQuoteCode 𝗣𝗔 f
        (fun n => ((unitFracPaperLUVSeq 𝗣𝗔).luv n).toLUV)
        (unitFracPaperLUVSeq 𝗣𝗔).rpnThresholdCodeSeq w weight_generable weight_mem).luv n).expect
          (liaHistory (paperDP 𝗣𝗔)) n :=
  lic_no_expected_net_update_conditional_paperLUV_closed 𝗣𝗔 f (unitFracPaperLUVSeq 𝗣𝗔) w
    weight_mem weight_generable

/-- **Fully closed instance of the `thm:ccee` paper rendering** — kind `N+` non-vacuity
witness, no hypothesis left standing.  Every binder is discharged by a named object: the
theory is `𝗣𝗔`, the source is the paper's own varying `1/(n+1)` literal LUV family, the
deferral function is `succDeferral`, and the weight is the harmonic sequence
`n ↦ 1/(n+1)` — non-constant (`harmonicWeight_not_constant`), `[0,1]`-valued
(`harmonicWeight_mem`) and ℙ‾-generable against every market
(`PGenerableRat.ofPolyRatCodes harmonicWeight_polyRatCodes`). -/
example :
    (fun n ↦ ((paperExactProductLUVSeq (unitFracPaperLUVSeq 𝗣𝗔)
        (deferredWeightPaperLUVSeq 𝗣𝗔 (paperMarketComputation 𝗣𝗔) succDeferral
          (fun n : ℕ => 1 / ((n : ℚ) + 1))
          (PGenerableRat.ofPolyRatCodes harmonicWeight_polyRatCodes
            (liaHistory (paperDP 𝗣𝗔)))
          harmonicWeight_mem)).luv n).toLUV.expect (liaHistory (paperDP 𝗣𝗔)) n) ≈ₙ
      fun n ↦ ((paperConditionalExpectationQuoteCode 𝗣𝗔 succDeferral
        (fun n => ((unitFracPaperLUVSeq 𝗣𝗔).luv n).toLUV)
        (unitFracPaperLUVSeq 𝗣𝗔).rpnThresholdCodeSeq (fun n : ℕ => 1 / ((n : ℚ) + 1))
        (PGenerableRat.ofPolyRatCodes harmonicWeight_polyRatCodes
          (liaHistory (paperDP 𝗣𝗔)))
        harmonicWeight_mem).luv n).expect (liaHistory (paperDP 𝗣𝗔)) n :=
  lic_no_expected_net_update_conditional_paperLUV_closed 𝗣𝗔 succDeferral
    (unitFracPaperLUVSeq 𝗣𝗔) (fun n : ℕ => 1 / ((n : ℚ) + 1)) harmonicWeight_mem
    (PGenerableRat.ofPolyRatCodes harmonicWeight_polyRatCodes (liaHistory (paperDP 𝗣𝗔)))

end LogicalInduction
