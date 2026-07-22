/-
# Integration test — discharging deference-corpus hypotheses (roadmap M3)

The downstream consumers (`deference-in-logical-induction`, `dose-response`) prove the
deference/dose-response *algebra* but take every Logical-Induction fact as a **named
hypothesis** over abstract `ℕ → ℝ` sequences, in their own `DeferenceAsymp` vocabulary
(`Approx` / `AsympLE`). This file is the roadmap's M3 integration test: *does our work
actually plug into that back end?* We check it three ways.

**Part A — vocabulary drop-in.** `DeferenceAsymp.Approx`/`AsympLE` are *definitionally* our
`Asymptotics.AsympEq`/`AsympLE` (`Tendsto (·−·) atTop (𝓝 0)` and the `ε`-form). We reproduce
a real deference theorem — `value_argmax_asymptotic` from `LeanDeference.lean` — verbatim in
*our* vocabulary and prove it with *our* combinators. It compiles, so `LogicalInduction.
Asymptotics` is a genuine drop-in for `DeferenceAsymp`. (Writing this test is what surfaced
the three combinators just added to `Asymptotics`: `AsympLE.trans`, `AsympLE.trans_asympEq`,
`AsympEq.finsetSum` — the corpus's `AsympLE.trans` / `trans_approx` / `approx_sum`.)

**Part B — price-level LI-content discharge.** `lic_deducible_tendsto_one` discharges a
Provability-Induction hypothesis of the exact downstream shape
`Approx (fun n => P n φ) (fun _ => 1)`. Part B wires that end to end.

**Part C — expectation-level interface and content.** Concrete `LUV.expectSeq` objects inhabit
the corpus's abstract expectation slots with no adapter, and `LUV.expect_converges` now
discharges convergence for one such sequence end to end. The stronger expectation relations
consumed by the reproduced Value theorem (`thm:cee`/`thm:expprovind`) are now proved M4
results; `thm:cee` explicitly requires its fixed-portfolio quote certificate, and this test
does not pretend convergence alone constructs that quotation interface.
-/
import LogicalInduction.Properties
import LogicalInduction.Framework.Expectations

namespace LogicalInduction.IntegrationTest

open LogicalInduction Filter Topology

/-! ## Part A — the deference asymptotics module is our `Asymptotics`

`DeferenceAsymp.Approx a b := Tendsto (fun n => a n - b n) atTop (𝓝 0)` is our `AsympEq`;
`DeferenceAsymp.AsympLE a b := ∀ ε>0, ∀ᶠ n, a n ≤ b n + ε` is our `AsympLE`. These `example`s
witness the definitional match, so their `≂ₙ`/`≲` are our `≈ₙ`/`≲ₙ`. -/

example (a b : ℕ → ℝ) : (a ≈ₙ b) = Tendsto (fun n => a n - b n) atTop (𝓝 0) := rfl
example (a b : ℕ → ℝ) : (a ≲ₙ b) = (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, a n ≤ b n + ε) := rfl

/-- **Reproduction of `DeferenceArgmax.value_argmax_asymptotic`** (from the deference
corpus's `LeanDeference.lean`), stated in *our* vocabulary and proved with *our* combinators.
Its named hypotheses are the LI theorems `thm:cee` (`hUM_S`, `hCee`) and `thm:expprovind`
(`hMon`); the conclusion is *Value*. That this typechecks against `LogicalInduction.
Asymptotics` is the interface check: our module supplies exactly the algebra the deference
proof runs on. -/
theorem value_argmax_asymptotic
    (ES Em Emi Eoi : ℕ → ℝ)
    (hUM_S : ES ≈ₙ Em)          -- thm:cee on the selected LUV Ŝ
    (hMon : Emi ≲ₙ Em)          -- thm:expprovind, from M ≥ mᵢ
    (hCee : Eoi ≈ₙ Emi) :       -- thm:cee on Oⁱ
    Eoi ≲ₙ ES :=
  ((hCee.asympLE).trans hMon).trans_asympEq hUM_S.symm

/-! ## Part B — discharging a Provability-Induction hypothesis for real

A downstream theorem that consumes `thm:provind` for a fixed deducible sentence would take a
hypothesis of the form `Approx (fun n => P n φ) (fun _ => 1)` — "the price of `φ` converges to
1". We model such a consumer and discharge its hypothesis from a *logical inductor*, with no
adapter: our `lic_deducible_tendsto_one` produces exactly that `AsympEq`. -/

/-- The shape of the LI fact a provind-consuming deference theorem names. -/
def ProvindHypothesis (P : History) (φ : Sentence) : Prop :=
  (fun n => P n φ) ≈ₙ (fun _ => 1)

/-- Our convergence theorem produces the named hypothesis exactly (`ConvergesTo … 1` is
`≈ₙ` against the constant `1`, by `convergesTo_iff_asympEq_const`). -/
lemma provind_hypothesis_discharged (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : Sentence) (hded : ∀ n, φ ∈ DP.D n)
    (hP1 : ∀ n, P n φ ≤ 1) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ProvindHypothesis P φ :=
  convergesTo_iff_asympEq_const.mp (lic_deducible_tendsto_one P DP φ hded hP1 hcons)

/-- The faithful sequence-level `thm:provind` consumer shape. Unlike the older direct
support lemma, deductions may arrive at arbitrary later stages. -/
def ProvindSequenceHypothesis (P : History) (φ ψ : ℕ → Sentence) : Prop :=
  ((fun n => P n (φ n)) ≈ₙ fun _ => 1) ∧
    ((fun n => P n (ψ n)) ≈ₙ fun _ => 0)

lemma provind_sequence_hypothesis_discharged
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ ψ : ℕ → Sentence)
    (hφ : PolySentenceCodes φ) (hψ : PolySentenceCodes ψ)
    (hthm : ∀ n, ∃ k, φ n ∈ DP.D k)
    (hdis : ∀ n, ∃ k, (∼ψ n) ∈ DP.D k)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ProvindSequenceHypothesis P φ ψ :=
  lic_provind P DP φ ψ hφ hψ hthm hdis hcons

/-- End-to-end wiring: a deference-style consumer that, *given* the provind hypothesis, draws
a conclusion (here the trivial `≲ₙ`-reflexivity stand-in for whatever it actually derives) —
composed with the discharge above, so under `[IsLogicalInductor P DP]` the consumer's LI
hypothesis is supplied entirely from our side. -/
example (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP] (φ : Sentence)
    (hded : ∀ n, φ ∈ DP.D n) (hP1 : ∀ n, P n φ ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (consumer : ProvindHypothesis P φ → (fun n => P n φ) ≲ₙ (fun _ => 1)) :
    (fun n => P n φ) ≲ₙ (fun _ => (1 : ℝ)) :=
  consumer (provind_hypothesis_discharged P DP φ hded hP1 hcons)

/-! ## Part C — closing the level gap: expectation-level interface

The corpus's *main* hypotheses are over expectations `E^H_n(X)`, which it treats as abstract
`ℕ → ℝ`. With the LUV bridge (`Expectations.lean`) those are now **concrete**: `E^H_n(X)` is
`X.expectSeq P`, a real sum of `P`'s prices on `X`'s threshold sentences. So the corpus's
`ES, Em, …` are literally `X.expectSeq P` for concrete LUVs, and its expectation hypotheses
`Approx (E_now X) (E_now Y)` are `X.expectSeq P ≈ₙ Y.expectSeq P` here — the *same* type. -/

/-- The corpus's `E_now(X) : ℕ → ℝ` slot is inhabited by our concrete expectation sequence. -/
noncomputable example (P : History) (X : LUV) : ℕ → ℝ := X.expectSeq P

/-- A `thm:cee`-shaped expectation hypothesis, in our concrete objects. -/
example (P : History) (X Y : LUV) : Prop := X.expectSeq P ≈ₙ Y.expectSeq P

/-- `thm:ec` now discharges convergence of a concrete expectation sequence end to end.
The compact threshold-code and world-value hypotheses are the explicit interfaces by which
the propositional model represents the paper's Θ-definable LUV. -/
theorem expectation_convergence_discharged (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (X : LUV) (hcode : X.PolyThresholdCodes)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → ∃ x, v.ValuesAt X x) :
    ∃ L, ConvergesTo (X.expectSeq P) L :=
  X.expect_converges P DP hcode hP hcons hval

#print axioms expectation_convergence_discharged
#print axioms provind_sequence_hypothesis_discharged

/-- **The deference `Value` theorem, applied to our concrete expectations.** Every abstract
`E_now(·)` slot in `value_argmax_asymptotic` is instantiated by `expectSeq P` of a concrete
LUV. The LI hypotheses (`thm:cee`/`thm:expprovind`) are still assumed here — proving them is
the property-tail work `Expectations.lean` states — but the *interface is closed*: the
corpus's expectation sequences are our objects, with no adapter and no type mismatch. -/
example (P : History) (Ŝ M mi Oi : LUV)
    (hUM_S : Ŝ.expectSeq P ≈ₙ M.expectSeq P)      -- thm:cee on the selected LUV
    (hMon  : mi.expectSeq P ≲ₙ M.expectSeq P)     -- thm:expprovind
    (hCee  : Oi.expectSeq P ≈ₙ mi.expectSeq P) :  -- thm:cee on Oⁱ
    Oi.expectSeq P ≲ₙ Ŝ.expectSeq P :=
  value_argmax_asymptotic _ _ _ _ hUM_S hMon hCee

/-! ## Part D — statistical expectation-property discharge

This checks the new LUV-combination property tail through the public roll-up rather than
only compiling its implementation file.  The first theorem exercises the reusable
Toeplitz hub; the second gives a downstream-consumer-shaped discharge of `thm:prandexp`. -/

theorem divergent_weighted_null_error_discharged
    {w e : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n)
    (hdiv : Tendsto (prefixSum w) atTop atTop)
    (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (weightedAverage w e) atTop (𝓝 0) :=
  LUVCombination.weightedAverage_tendsto_zero_of_tendsto_zero hw0 hdiv he

def PseudorandomExpectationHypothesis
    (As : ℕ → LUVCombination) (P : History) : Prop :=
  (fun n => (As n).expect P n) ≳ₙ (fun _ => 0)

lemma prandexp_hypothesis_discharged
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (hexact : LUVCombination.ExactTheoryPresentation As DP)
    {truth : ℕ → ℝ}
    (hdet : LUVCombination.DeterminedViaTheory As P DP truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction)
    (clock : PatientSettlementClock (LUVCombination.normalizedMesh As b) P DP
      (LUVCombination.normalizedMeshTruth As P DP hworld b) f)
    (hpseudo : PseudorandomAbove truth f P)
    (hverify : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (LUVCombination.normalizedMesh As b) (h.normalizedMesh_poly b)
        W hWgen P DP)
    (hverifyNeg : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (fun n => (LUVCombination.normalizedMesh As b n).neg)
        (h.normalizedMesh_poly b).neg W hWgen P DP) :
    PseudorandomExpectationHypothesis As P :=
  h.prandexp hexact hdet b hshare hP hworld f clock hpseudo hverify hverifyNeg

#print axioms divergent_weighted_null_error_discharged
#print axioms prandexp_hypothesis_discharged

/-! ## Part E — arbitrary-BCS affine statistical capstones

These downstream-shaped wrappers ensure the public paper declarations consume an actual
arbitrary-bound `BoundedCombinationSequence`; the unit-risk hubs are not accidentally used
as the advertised statements. -/

theorem arbitrary_bcs_recunbiasedaff_discharged
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : AffineCombination.BoundedCombinationSequence As P)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {truth : ℕ → ℝ} (hdet : AffineCombination.DeterminedViaTheory As P DP truth)
    (hWdiv : DivergentWeighting W P)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hverify : AffineCombination.BiasRunHistoricallyVerifiable
      (fun n => (As n).scale (.const h.unitNormalization.scale))
      (h.poly.scaleRat h.unitNormalization.scale) W hWgen P DP)
    (hverifyNeg : AffineCombination.BiasRunHistoricallyVerifiable
      (fun n => ((As n).scale (.const h.unitNormalization.scale)).neg)
      (h.poly.scaleRat h.unitNormalization.scale).neg W hWgen P DP) :
    HasLimitPoint (weightedBias (fun i => (W i).denote P)
      (fun i => (As i).price P i) truth) 0 :=
  h.recunbiasedaff hWgen hdet hWdiv hworld hP hverify hverifyNeg

lemma arbitrary_bcs_wubaff_discharged
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : AffineCombination.BoundedCombinationSequence As P)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    {truth : ℕ → ℝ} (hdet : AffineCombination.DeterminedViaTheory As P DP truth)
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f)
    (hsupport : WeightingSupportedOnDeferralImage W P f)
    (emit : AffineCombination.FeedbackTraderEmissionSigns
      (h.poly.scaleRat h.unitNormalization.scale) hW hstrict)
    (bridge : AffineCombination.FeedbackTruthSequence
      (fun n => (As n).scale (.const h.unitNormalization.scale))
      (fun n => (h.unitNormalization.scale : ℝ) * truth n) P DP f)
    (hWdiv : DivergentWeighting W P)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    weightedBias (fun i => (W i).denote P)
      (fun i => (As i).price P i) truth ≈ₙ (fun _ => 0) :=
  h.wubaff hW hdet hstrict hsupport emit bridge hWdiv hP hworld

lemma arbitrary_bcs_prandaff_discharged
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : AffineCombination.BoundedCombinationSequence As P)
    {truth : ℕ → ℝ} (hdet : AffineCombination.DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (f : DeferralFunction)
    (clock : PatientSettlementClock
      (fun n => (As n).scale (.const h.unitNormalization.scale)) P DP
      (fun n => (h.unitNormalization.scale : ℝ) * truth n) f)
    (hpseudo : Pseudorandom truth f P)
    (hverify : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (fun n => (As n).scale (.const h.unitNormalization.scale))
        (h.poly.scaleRat h.unitNormalization.scale) W hWgen P DP)
    (hverifyNeg : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (fun n => ((As n).scale (.const h.unitNormalization.scale)).neg)
        (h.poly.scaleRat h.unitNormalization.scale).neg W hWgen P DP)
    (hverifyNegNeg : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (fun n => (((As n).scale (.const h.unitNormalization.scale)).neg).neg)
        (h.poly.scaleRat h.unitNormalization.scale).neg.neg W hWgen P DP) :
    (fun n => (As n).price P n) ≈ₙ (fun _ => 0) :=
  h.prandaff hdet hworld hP f clock hpseudo hverify hverifyNeg hverifyNegNeg

#print axioms arbitrary_bcs_recunbiasedaff_discharged
#print axioms arbitrary_bcs_wubaff_discharged
#print axioms arbitrary_bcs_prandaff_discharged

end LogicalInduction.IntegrationTest
