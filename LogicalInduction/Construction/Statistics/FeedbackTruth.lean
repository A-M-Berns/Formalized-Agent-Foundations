import LogicalInduction.Construction.Statistics.FeedbackEmission
import LogicalInduction.Construction.Quotation.DeferralFibre
import LogicalInduction.Framework.Emission.WriteOut

/-!
# Concrete delayed feedback truth for `thm:wub`, `thm:wubaff` and `thm:wubexp`

The completed-theory value stream in `DeterminedViaTheory` is semantic data, not a
computable oracle.  This file renders the delayed-feedback half of `thm:wub` (tex:1249),
`thm:wubaff` (tex:1480) and `thm:wubexp` (tex:1822): the paper's separate operational
premise that `thmval` of the day's combination can be computed in time `O(f(n+1))`.

`FeedbackTruthComputation truth f` is that premise — a rational value stream, a value-code
stream, and a `MachineDigits` bound read at the unary pair `⟨k, f (k+1)⟩`, whose length is
the paper's own `O(f(k+1))` meter.
The semantic agreement `value k = truth (f k)` is recorded only on the required indices, and
the certificate carries no price-accuracy, unbiasedness, convergence, or logical-inductor
conclusion; uniform normalization and market bounds remain separate inputs to the public
constructor.

The premise is inhabited, at three strengths.  `ordinaryFeedbackTruthComputation` is the
constant witness; `alternatingFeedbackTruthComputation_nonempty` and
`exists_nonconstant_feedbackTruthComputation` give a genuinely two-valued stream, so the
endpoints' dependence on `truth` is exercised by an actual inhabitant; and
`unboundedFeedbackTruthComputation_nonempty` and
`exists_unbounded_feedbackTruthComputation` give a stream ranging over **unboundedly many**
rationals — the `k`th deferred value is `(k : ℚ)`, and the truth stream it matches is
unbounded above along the deferral image.  Nothing about the `computes` field stands in the
way of that: `MachineDigits` bounds the symbols a poly-time writer must emit, never the
magnitude of the value written.  The unbounded witness's certificate is
`ratNatCast_machineDigits` (`Properties/OccamBounds.lean`) at `UnaryRuler.unpairFst` —
`⌜(n : ℚ)⌝ = ⟪2n, 1⟫`, hence `MachineDigits.natPair` of two rulers — and the general route
for an arbitrary rational stream is `MachineRatCodes.toMachineDigits`
(`Framework/Machine/WriteOutMachine.lean`), which assembles `⌜q n⌝` from the class's
numerator-code and denominator runs.

`feedbackFlag`, `feedbackIndex` and `sourceIndex` recover the source component of a delayed
feedback day through the bounded deferral evaluator, never through an unbounded inverse of
`f`; they need only `StrictlyIncreasingDeferral`, which `thm:wubaff` itself supplies.

`feedbackResidualSeq As C` is the emitted object: the sparse literal affine family
carrying `A_{f k} - truth (f k)` on day `f (k+1)` and the zero combination on every other
day, with `feedbackResidualSeqPoly` its uniform polynomial syntax emitter (`dd:fuel`) and
`truthCodeAt_eq_of_flag` proving the emitted rational payload is the canonical code.

`feedbackResidualSeq_value_vanishing` and `feedbackResidualSeq_bounded` feed
`feedbackTruthSequence`, which builds the `FeedbackTruthSequence` boundary at
`ApproxDeterminedViaTheory`.  `feedbackTruthSequence_ofDetermined` is the exact (`err = 0`)
instance used by the sentence and affine lanes; the LUV mesh needs the approximate form
(`dd:mesh`).

The endpoints are `lic_wubaff_ofComputation`, `lic_wub_ofComputation`,
`boundedCombination_wubaff_ofComputation` and `luv_wubexp_ofComputation`, each universal
over `[IsLogicalInductor P DP]`.  `Endpoints.lean` lifts all four to the
`_unconditional` forms over the `LIA`, and `Construction/LUV/Endpoints.lean` consumes the last
of them.

One paper defect is carried here: `thm:wubexp`'s `hsupport` clause is printed at
`thm:recurringunbiasednessexp` instead (`PE2`, `notes/paper-errata.md`), and
`luv_wubexp_ofComputation` states it at the feedback theorem where it belongs.

**Cross-lane edge.**  This module imports `Construction/Quotation/DeferralFibre.lean` for the
deferral fibre `deferralPreimage` (with `_at`, `_spec` and `unaryRuler_`) and the image flag
beside it.  It is the only edge between the two lanes, and it runs one way: nothing in
`Quotation/` reaches `Statistics/`, since the schedule both need is stated upstream of both in
`Properties/SelfTrust.lean`.  `DeferralFibre.lean` records the boundary from the `Quotation/`
side.  This module's own `Construction/Statistics/FeedbackEmission.lean` import is in-lane —
it supplies `scheduledDeferral`, `feedbackTraderEmissionSigns` and the two `_ofFeedbackTruth`
consumers below.

`Nat.sqrt` is locally irreducible in the namespace below, for the reason stated in
`Construction/Statistics/SettlementClock.lean`; a declaration moved across that boundary must
carry the attribute with it.
**The criterion binder below is `def:lic` at the paper's own quantifier.**  Every result here that consumes an
exploiting trader takes `[IsLogicalInductor P DP]`, and the trader is certified at `EfficientlyComputable`:
it is assembled from `AffineCombination.PolySequence`'s machine-metered emission fields
through `PolySequence.buyBelowTrader_ec` (`Properties/AffineCoherence.lean`), which has no
fuel-class form: the bridge `BigSpliceStream.toMachine` runs fuel to machine, and no map
back is proved or claimed.  The
calibration is stated at `def:ec` in `Framework/Affine.lean`, and the `_unconditional`
endpoints discharge the criterion through `LIA_is_logical_inductor`.

-/

namespace LogicalInduction
namespace FeedbackTruth

open AffineCombination PrefixPatchCompile Filter Topology

-- See the module header on `Nat.sqrt` opacity.
attribute [local irreducible] Nat.sqrt

/-! ## The delayed-truth premise -/

/-- The paper's delayed truth computation premise.  Input `k` names the value of
`A_{f k}`; the program must return its canonical rational code within `O(f(k+1))` time
(tex:1251).  The clause is rendered **at the machine model**, on the input that carries the
bound: the code stream is read at the unary pair `⟨k, f (k+1)⟩`, whose length is
`Nat.pair k (f (k+1)) ≥ f (k+1)`, so "polynomial in the input length" is a bound in the
deferral value rather than in the day.

**This is a relaxation of the paper's clause, not a restatement of it.**  The paper asks for
*linear* time `O(f(k+1))`; polynomial time in the length of `⟨k, f (k+1)⟩` is implied by that
and does not imply it back.  The field is therefore a **weaker** hypothesis than the printed
premise, and every endpoint taking it is correspondingly **stronger** — the direction a
relaxed hypothesis has to run for the rendering to be safe.  The relaxation is deliberate:
`Complexity.FP` is a polynomial-time class and has no linear-time form.

The certificate is total — `MachineDigits code` meters *every* paired index, not only the
deferred ones — and this costs nothing: a program meeting the paper's clause on the deferred
inputs can be clocked by the same polynomial in the input's length at every input, answering
`0` on a timeout, which agrees with it on the deferred inputs and is machine-metered
everywhere.  `computes_at` is what pins the answers, and the equality with the semantic real
stream is recorded only on the required indices.
Paper node: `thm:wubaff`, `thm:wubexp` -/
structure FeedbackTruthComputation (truth : ℕ → ℝ) (f : DeferralFunction) where
  /-- The delayed value stream. -/
  value : ℕ → ℚ
  /-- The written-out value code, read at the paired index `⟨component, day⟩`. -/
  code : ℕ → ℕ
  /-- The code stream is machine-metered: polynomial time in the length of the unary pair,
  which on the deferred input `⟨k, f (k+1)⟩` is the paper's `O(f(k+1))`. -/
  computes : MachineDigits code
  /-- On the deferred day `f (k+1)` the stream returns the canonical code of the `k`th
  value. -/
  computes_at : ∀ k, code (Nat.pair k (f (k + 1))) = Encodable.encode (value k)
  /-- The values are the semantic truths along the deferral. -/
  agrees : ∀ k, (value k : ℝ) = truth (f k)

/-! ## Non-vacuity witnesses -/

/-- **The delayed-truth premise is inhabited, for every deferral schedule `f`:** the code
stream is the constant `⌜(1 : ℚ)⌝`, and a fixed word is written by a machine that ignores
its input, which is `MachineDigits.const`.  No clock is read and the schedule `f` plays no
part in the certificate — it is total in the paired index, so `computes_at` holds at every
`k` by `rfl`.  Kind `N+`, provenance (a).

Disclosure: this witness is **degenerate in the value stream** — `value` and `truth` are
both constant — so on its own it establishes satisfiability of the premise and nothing
about the endpoints' dependence on `truth`.  That dependence is exercised by
`alternatingFeedbackTruthComputation_nonempty` below, whose stream takes both values along
the deferral image, and by `unboundedFeedbackTruthComputation_nonempty`, whose stream ranges
over unboundedly many rationals.  The last of those is not a harder metering problem than
this one: `MachineDigits` bounds the symbols a poly-time writer must emit, not the magnitude
of the value, so `ratNatCast_machineDigits` certifies `k ↦ (k : ℚ)` outright, and
`MachineRatCodes.toMachineDigits` is the general route for an arbitrary rational stream.
Paper node: `thm:wub`, `thm:wubaff`, `thm:wubexp` -/
def ordinaryFeedbackTruthComputation (f : DeferralFunction) :
    FeedbackTruthComputation (fun _ => (1 : ℝ)) f where
  value _ := 1
  code _ := Encodable.encode (1 : ℚ)
  computes := MachineDigits.const _
  computes_at _ := rfl
  agrees k := by norm_num

/-! ### A non-degenerate delayed-truth witness

`ordinaryFeedbackTruthComputation` inhabits the premise but says nothing about a varying
value stream.  The witness below carries a genuinely two-valued stream — `1` at even
feedback indices, `0` at odd — so the endpoints' dependence on `truth` is exercised by an
inhabitant, not only by the arbitrary-`truth` statement.  The program is a parity test
(`BigDigits.mod_two` on the identity) feeding a two-way `ifzSel` between the two constant
rational codes; that is a fuel-metered *certification device*, carried to the machine
reading by `BigDigits.toMachine`. -/

private lemma parity_polyFueled : ∃ c, PolyFueled c (fun k => k % 2) :=
  BigDigits.mod_two (BigDigits.of_polyFueled PolyFueled.id)

private lemma twoValued_polyFueled (A B : ℕ) :
    ∃ c, PolyFueled c (fun k => if k % 2 = 0 then A else B) := by
  obtain ⟨cp, hp⟩ := parity_polyFueled
  refine ⟨_, (ifzSel_polyFueled.comp
    (((PolyFueled.const A).pair (PolyFueled.const B)).pair hp)).of_eq (fun k => ?_)⟩
  simp only [Nat.unpair_pair, ifzSelFn]

/-- The alternating feedback value stream: the value of the `k`th deferred component is
`1` for even `k` and `0` for odd `k`. -/
def alternatingValue (k : ℕ) : ℚ := if k % 2 = 0 then 1 else 0

private lemma alternatingValue_polyFueled :
    ∃ c, PolyFueled c (fun k => Encodable.encode (alternatingValue k)) := by
  obtain ⟨c, hc⟩ :=
    twoValued_polyFueled (Encodable.encode (1 : ℚ)) (Encodable.encode (0 : ℚ))
  exact ⟨c, hc.of_eq fun k => by
    by_cases h : k % 2 = 0 <;> simp [alternatingValue, h]⟩

open scoped Classical in
/-- The semantic truth stream matched to `alternatingValue` along `f`: `1` exactly on the
even part of the deferral image, `0` everywhere else. -/
noncomputable def alternatingTruth (f : DeferralFunction) (n : ℕ) : ℝ :=
  if ∃ k, f k = n ∧ k % 2 = 0 then 1 else 0

private lemma alternatingTruth_apply {f : DeferralFunction}
    (hstrict : StrictlyIncreasingDeferral f) (k : ℕ) :
    alternatingTruth f (f k) = ((alternatingValue k : ℚ) : ℝ) := by
  classical
  by_cases h : k % 2 = 0
  · have : ∃ j, f j = f k ∧ j % 2 = 0 := ⟨k, rfl, h⟩
    simp [alternatingTruth, alternatingValue, this, h]
  · have : ¬ ∃ j, f j = f k ∧ j % 2 = 0 := by
      rintro ⟨j, hj, hj2⟩
      exact h (hstrict.injective hj ▸ hj2)
    simp [alternatingTruth, alternatingValue, this, h]

/-- The alternating value codes, read off the component half of the paired index. -/
private lemma alternatingCode_machineDigits :
    MachineDigits (fun z => Encodable.encode (alternatingValue z.unpair.1)) := by
  obtain ⟨c, hc⟩ := alternatingValue_polyFueled
  exact (BigDigits.of_polyFueled (hc.comp PolyFueled.left)).toMachine

/-- **The delayed-truth premise is inhabited by a stream that actually varies:** the
alternating value stream, machine-metered on the paired index.  The metering is generic —
the value codes are two constants selected by a parity test, which is polynomial time in the
pair's length whatever the deferral schedule is.  Kind `N+`, provenance (a).
Paper node: `thm:wub`, `thm:wubaff`, `thm:wubexp` -/
lemma alternatingFeedbackTruthComputation_nonempty {f : DeferralFunction}
    (hstrict : StrictlyIncreasingDeferral f) :
    Nonempty (FeedbackTruthComputation (alternatingTruth f) f) :=
  ⟨{ value := alternatingValue
     code := fun z => Encodable.encode (alternatingValue z.unpair.1)
     computes := alternatingCode_machineDigits
     computes_at := fun k => by simp
     agrees := fun k => (alternatingTruth_apply hstrict k).symm }⟩

/-- The alternating witness is genuinely non-constant on the deferral image: the theorem's
`truth` argument takes both values at inhabited instances. -/
lemma exists_nonconstant_feedbackTruthComputation {f : DeferralFunction}
    (hstrict : StrictlyIncreasingDeferral f) :
    ∃ truth : ℕ → ℝ, Nonempty (FeedbackTruthComputation truth f) ∧
      truth (f 0) = 1 ∧ truth (f 1) = 0 := by
  refine ⟨alternatingTruth f, alternatingFeedbackTruthComputation_nonempty hstrict, ?_, ?_⟩
  · simpa [alternatingValue] using alternatingTruth_apply hstrict 0
  · simpa [alternatingValue] using alternatingTruth_apply hstrict 1

/-! ### An unboundedly-valued delayed-truth witness

The two witnesses above range over one and two rational values.  The one below ranges over
*unboundedly many*: the `k`th deferred component has value `(k : ℚ)`, so the `truth`
argument it instantiates is unbounded above along the deferral image.

The certificate is not a harder problem than the alternating one's, and no `Encodable ℚ`
normal form is needed for it.  `MachineDigits` meters the *symbols* a poly-time writer must
emit, never the magnitude of the value written, and `ratNatCast_machineDigits`
(`Properties/OccamBounds.lean`) meters the rational cast of any unary ruler outright:
`⌜(n : ℚ)⌝ = ⟪2n, 1⟫` (`encode_rat_natCast`), which is `MachineDigits.natPair` of the doubled
ruler and the constant `1`.  Here the ruler is `UnaryRuler.unpairFst`, the component half of
the paired index.  For a stream of *freely varying* rationals the general route is
`MachineRatCodes.toMachineDigits`, which assembles `⌜q n⌝` from that class's numerator-code
and denominator runs. -/

open scoped Classical in
/-- The semantic truth stream matched to the unbounded value stream along `f`: the source
index of a deferral day, and `0` off the deferral image. -/
noncomputable def unboundedTruth (f : DeferralFunction) (n : ℕ) : ℝ :=
  if h : ∃ k, f k = n then ((h.choose : ℕ) : ℝ) else 0

private lemma unboundedTruth_apply {f : DeferralFunction}
    (hstrict : StrictlyIncreasingDeferral f) (k : ℕ) :
    unboundedTruth f (f k) = ((k : ℕ) : ℝ) := by
  classical
  have hex : ∃ j, f j = f k := ⟨k, rfl⟩
  rw [unboundedTruth, dif_pos hex]
  have hchoose := hstrict.injective hex.choose_spec
  rw [hchoose]

/-- The unbounded value codes, read off the component half of the paired index. -/
private lemma unboundedCode_machineDigits :
    MachineDigits (fun z => Encodable.encode (((z.unpair.1 : ℕ) : ℚ))) :=
  ratNatCast_machineDigits UnaryRuler.unpairFst

/-- **The delayed-truth premise is inhabited by a stream ranging over unboundedly many
rationals:** the `k`th deferred value is `(k : ℚ)`, whose code the program reads off the
component half of the paired index.  The metering is generic — it is the rational cast of a
unary ruler, polynomial time in the pair's length whatever the deferral schedule is — and
nothing in it bounds the value stream.  Kind `N+`, provenance (a).
Paper node: `thm:wub`, `thm:wubaff`, `thm:wubexp` -/
lemma unboundedFeedbackTruthComputation_nonempty {f : DeferralFunction}
    (hstrict : StrictlyIncreasingDeferral f) :
    Nonempty (FeedbackTruthComputation (unboundedTruth f) f) :=
  ⟨{ value := fun k => ((k : ℕ) : ℚ)
     code := fun z => Encodable.encode (((z.unpair.1 : ℕ) : ℚ))
     computes := unboundedCode_machineDigits
     computes_at := fun k => by simp
     agrees := fun k => by rw [unboundedTruth_apply hstrict k]; push_cast; ring }⟩

/-- The unbounded witness's `truth` argument is unbounded above along the deferral image, so
the endpoints' dependence on `truth` is exercised by an inhabitant taking arbitrarily large
values — not only by a finitely-valued one. -/
lemma exists_unbounded_feedbackTruthComputation {f : DeferralFunction}
    (hstrict : StrictlyIncreasingDeferral f) :
    ∃ truth : ℕ → ℝ, Nonempty (FeedbackTruthComputation truth f) ∧
      ∀ B : ℝ, ∃ k, B < truth (f k) := by
  refine ⟨unboundedTruth f, unboundedFeedbackTruthComputation_nonempty hstrict, fun B => ?_⟩
  obtain ⟨k, hk⟩ := exists_nat_gt B
  exact ⟨k, by rw [unboundedTruth_apply hstrict k]; exact_mod_cast hk⟩

/-! ## The shifted deferral schedule -/

/-- The source component on a delayed feedback day: the preimage of `m`, minus one. -/
def feedbackIndex (f : DeferralFunction) (m : ℕ) : ℕ :=
  deferralPreimage f m - 1

/-- A day is active exactly when it is `f(j)` for a positive index `j`.
Natural-valued Booleans keep the schedule inside the polynomial compiler. -/
def feedbackFlag (f : DeferralFunction) (m : ℕ) : ℕ :=
  if deferralImageFlag f m = 0 then 0
  else if deferralPreimage f m = 0 then 0 else 1

lemma unaryRuler_feedbackIndex (f : DeferralFunction) :
    UnaryRuler (feedbackIndex f) :=
  ((unaryRuler_deferralPreimage f).sub (UnaryRuler.const 1)).of_eq
    (fun m => by simp [feedbackIndex])

lemma unaryRuler_feedbackFlag (f : DeferralFunction) :
    UnaryRuler (feedbackFlag f) :=
  ((unaryRuler_deferralImageFlag f).ifZero (UnaryRuler.const 0)
    ((unaryRuler_deferralPreimage f).ifZero (UnaryRuler.const 0)
      (UnaryRuler.const 1))).of_eq (fun m => by simp [feedbackFlag])

lemma feedbackFlag_zero_or_one (f : DeferralFunction) (m : ℕ) :
    feedbackFlag f m = 0 ∨ feedbackFlag f m = 1 := by
  unfold feedbackFlag
  by_cases hi : deferralImageFlag f m = 0
  · simp [hi]
  · by_cases hp : deferralPreimage f m = 0
    · simp [hi, hp]
    · simp [hi, hp]

lemma feedbackFlag_at
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (k : ℕ) : feedbackFlag f (f (k + 1)) = 1 := by
  rw [feedbackFlag,
    deferralImageFlag_at f (k + 1),
    deferralPreimage_at f hstrict.injective (k + 1)]
  simp

lemma feedbackIndex_at
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (k : ℕ) : feedbackIndex f (f (k + 1)) = k := by
  rw [feedbackIndex, deferralPreimage_at f hstrict.injective (k + 1)]
  omega

/-- On every active day, the shifted schedule really names a unique feedback component. -/
lemma feedbackFlag_spec
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    {m : ℕ} (hm : feedbackFlag f m = 1) :
    f (feedbackIndex f m + 1) = m := by
  have himage : deferralImageFlag f m = 1 := by
    unfold feedbackFlag at hm
    split at hm <;> rename_i hflag
    · omega
    · rcases deferralImageFlag_zero_or_one f m with hz | ho
      · exact (hflag hz).elim
      · exact ho
  have hpre : deferralPreimage f m ≠ 0 := by
    unfold feedbackFlag at hm
    rw [if_neg (by omega)] at hm
    split at hm <;> omega
  have hpair := deferralPreimage_spec f hstrict.injective himage
  rw [feedbackIndex]
  have hpos : 1 ≤ deferralPreimage f m := Nat.one_le_iff_ne_zero.2 hpre
  rw [Nat.sub_add_cancel hpos]
  exact hpair.2

/-- The source affine index is recovered by the same bounded deferral evaluator used by
the feedback-trader emitter; no unbounded inverse of `f` is evaluated. -/
def sourceIndex (f : DeferralFunction) (m : ℕ) : ℕ :=
  FeedbackEmission.scheduledDeferral f m (feedbackIndex f m)

lemma unaryRuler_sourceIndex (f : DeferralFunction) :
    UnaryRuler (sourceIndex f) :=
  ((unaryRuler_scheduledValue f).comp
    (UnaryRuler.id.pair (unaryRuler_feedbackIndex f))).of_eq
    (fun m => by simp [sourceIndex, FeedbackEmission.scheduledDeferral])

lemma sourceIndex_at
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (k : ℕ) : sourceIndex f (f (k + 1)) = f k := by
  rw [sourceIndex, feedbackIndex_at f hstrict k]
  apply FeedbackEmission.scheduledDeferral_eq f
  exact (hstrict (Nat.lt_succ_self k)).le

lemma sourceIndex_le_of_flag
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    {m : ℕ} (hm : feedbackFlag f m = 1) :
    sourceIndex f m < m := by
  have hdeadline := feedbackFlag_spec f hstrict hm
  have hkn : f (feedbackIndex f m) ≤ m := by
    calc
      f (feedbackIndex f m) ≤ f (feedbackIndex f m + 1) :=
        (hstrict (Nat.lt_succ_self _)).le
      _ = m := hdeadline
  have hsource : sourceIndex f m = f (feedbackIndex f m) := by
    exact FeedbackEmission.scheduledDeferral_eq f hkn
  calc
    sourceIndex f m = f (feedbackIndex f m) := hsource
    _ < f (feedbackIndex f m + 1) := hstrict (Nat.lt_succ_self _)
    _ = m := hdeadline

lemma sourceIndex_eq_of_flag
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    {m : ℕ} (hm : feedbackFlag f m = 1) :
    sourceIndex f m = f (feedbackIndex f m) := by
  have hdeadline := feedbackFlag_spec f hstrict hm
  apply FeedbackEmission.scheduledDeferral_eq f
  calc
    f (feedbackIndex f m) ≤ f (feedbackIndex f m + 1) :=
      (hstrict (Nat.lt_succ_self _)).le
    _ = m := hdeadline

/-! ## Bounded truth-code simulation -/

/-- Canonical rational code returned by the delayed truth computation on day `m`: its code
stream read at the pair `⟨source component, day⟩`. -/
def truthCodeAt {truth : ℕ → ℝ} {f : DeferralFunction}
    (C : FeedbackTruthComputation truth f) (m : ℕ) : ℕ :=
  C.code (Nat.pair (feedbackIndex f m) m)

lemma machineDigits_truthCodeAt {truth : ℕ → ℝ} {f : DeferralFunction}
    (C : FeedbackTruthComputation truth f) :
    MachineDigits (truthCodeAt C) :=
  C.computes.comp ((unaryRuler_feedbackIndex f).pair UnaryRuler.id)

lemma truthCodeAt_eq_of_flag
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    {m : ℕ} (hm : feedbackFlag f m = 1) :
    truthCodeAt C m = Encodable.encode (C.value (feedbackIndex f m)) := by
  have hdeadline := feedbackFlag_spec f hstrict hm
  have hrun := C.computes_at (feedbackIndex f m)
  rw [hdeadline] at hrun
  exact hrun

/-! ## Literal sparse affine syntax -/

/-- The feedback residual family: on an active day the source combination `A_{f k}`
centred at the computed value of `truth (f k)`, and the literal zero affine combination on
every other day. -/
def feedbackResidualSeq {truth : ℕ → ℝ} {f : DeferralFunction}
    (As : ℕ → AffineCombination) (C : FeedbackTruthComputation truth f)
    (m : ℕ) : AffineCombination :=
  if feedbackFlag f m = 0 then
    ⟨EF.const 0, []⟩
  else
    ⟨EF.add (As (sourceIndex f m)).const
        (EF.mul (EF.const (-1)) (EF.const (C.value (feedbackIndex f m)))),
      (As (sourceIndex f m)).terms⟩

lemma feedbackResidualSeq_eq_at
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (As : ℕ → AffineCombination) (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    (k : ℕ) :
    feedbackResidualSeq As C (f (k + 1)) =
      ⟨EF.add (As (f k)).const (EF.mul (EF.const (-1)) (EF.const (C.value k))),
        (As (f k)).terms⟩ := by
  rw [feedbackResidualSeq, feedbackFlag_at f hstrict k, if_neg one_ne_zero,
    sourceIndex_at f hstrict k, feedbackIndex_at f hstrict k]

@[simp] lemma feedbackResidualSeq_price_at
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (As : ℕ → AffineCombination) (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    (P : History) (k : ℕ) :
    (feedbackResidualSeq As C (f (k + 1))).price P (f (k + 1)) =
      (As (f k)).price P (f (k + 1)) - (C.value k : ℝ) := by
  rw [feedbackResidualSeq_eq_at As C hstrict k]
  simp [AffineCombination.price, AffineCombination.value]
  ring

@[simp] lemma feedbackResidualSeq_magnitude
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (As : ℕ → AffineCombination) (C : FeedbackTruthComputation truth f)
    (m : ℕ) (P : History) :
    (feedbackResidualSeq As C m).magnitude P =
      if feedbackFlag f m = 0 then 0
      else (As (sourceIndex f m)).magnitude P := by
  unfold feedbackResidualSeq AffineCombination.magnitude
  split <;> simp

/-! ### Polynomial affine-sequence certificate -/

/-- The sparse literal sequence has a uniform polynomial syntax emitter.  The rational
payload on an active branch is emitted directly from the bounded universal evaluator;
`truthCodeAt_eq_of_flag` proves that payload is the canonical code appearing in the syntax. -/
noncomputable def feedbackResidualSeqPoly
    {As : ℕ → AffineCombination} (hA : PolySequence As)
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f) :
    PolySequence (feedbackResidualSeq As C) := by
  have hflagR := unaryRuler_feedbackFlag f
  have hsourceR := unaryRuler_sourceIndex f
  have htruth := machineDigits_truthCodeAt C
  let count : ℕ → ℕ := fun m =>
    if feedbackFlag f m = 0 then 0 else hA.termCount (sourceIndex f m)
  let coeff : ℕ → EF := fun z =>
    hA.coefficient (Nat.pair (sourceIndex f z.unpair.1) z.unpair.2)
  let sentence : ℕ → Sentence := fun z =>
    hA.sentence (Nat.pair (sourceIndex f z.unpair.1) z.unpair.2)
  have hqueryR : UnaryRuler (fun z : ℕ =>
      Nat.pair (sourceIndex f z.unpair.1) z.unpair.2) :=
    (hsourceR.comp UnaryRuler.unpairFst).pair UnaryRuler.unpairSnd
  have hcountPoly : UnaryRuler count :=
    (hflagR.ifZero (UnaryRuler.const 0) (hA.termCount_poly.comp hsourceR)).of_eq
      (fun m => by simp [count])
  have hcoeffPoly : MachineSpliceStream (fun z => (coeff z).serialize) := by
    simpa only [coeff] using hA.coefficient_poly.comp
      (f := fun z : ℕ => Nat.pair (sourceIndex f z.unpair.1) z.unpair.2) hqueryR
  have hsentencePoly : MachineSentenceCodes sentence :=
    (hA.sentence_poly.comp
      (f := fun z : ℕ => Nat.pair (sourceIndex f z.unpair.1) z.unpair.2)
      hqueryR).of_eq (fun z => rfl)
  have hrawConst : MachineSpliceStream (fun m => [1, truthCodeAt C m]) :=
    MachineSpliceStream.bigPayload 1 (Or.inl rfl) htruth
  have hminusRaw : MachineSpliceStream (fun m =>
      (EF.const (-1)).serialize ++ [1, truthCodeAt C m] ++ [3]) :=
    ((MachineSpliceStream.serialize_const (-1)).append hrawConst).append
      (MachineSpliceStream.tag 3 (by norm_num))
  have hactiveRaw : MachineSpliceStream (fun m =>
      (As (sourceIndex f m)).const.serialize ++
        ((EF.const (-1)).serialize ++ [1, truthCodeAt C m] ++ [3]) ++ [2]) :=
    ((hA.const_poly.comp (f := fun m : ℕ => sourceIndex f m) hsourceR).append
      hminusRaw).append (MachineSpliceStream.tag 2 (by norm_num))
  have hconstIf := MachineSpliceStream.ifZero
    (MachineSpliceStream.serialize_const 0) hactiveRaw
    (t := fun m : ℕ => feedbackFlag f m) hflagR
  exact {
    termCount := count
    coefficient := coeff
    sentence := sentence
    termCount_poly := hcountPoly
    const_poly := by
      refine MachineSpliceStream.of_eq hconstIf ?_
      intro m
      by_cases hm : feedbackFlag f m = 0
      · simp [feedbackResidualSeq, hm]
      · have hm1 : feedbackFlag f m = 1 :=
          (feedbackFlag_zero_or_one f m).resolve_left hm
        rw [truthCodeAt_eq_of_flag C hstrict hm1]
        simp [feedbackResidualSeq, hm, EF.serialize, List.append_assoc]
    coefficient_poly := hcoeffPoly
    sentence_poly := hsentencePoly
    terms_eq := by
      intro m
      unfold feedbackResidualSeq count coeff sentence
      by_cases hm : feedbackFlag f m = 0
      · simp [hm]
      · simp [hm, hA.terms_eq]
    const_rank := by
      intro m
      unfold feedbackResidualSeq
      by_cases hm : feedbackFlag f m = 0
      · simp [hm]
      · rw [if_neg hm]
        simp only [EF.rank]
        have hone : feedbackFlag f m = 1 :=
          (feedbackFlag_zero_or_one f m).resolve_left hm
        have hsle := (sourceIndex_le_of_flag f hstrict hone).le
        exact Nat.max_le.mpr ⟨hA.const_rank _ |>.trans hsle, by simp⟩
    coefficient_rank := by
      intro m j hj
      unfold count at hj
      have hm : feedbackFlag f m = 1 := by
        rcases feedbackFlag_zero_or_one f m with hz | ho
        · simp [hz] at hj
        · exact ho
      have hsle := (sourceIndex_le_of_flag f hstrict hm).le
      unfold coeff
      simp only [Nat.unpair_pair]
      exact (hA.coefficient_rank _ j (by simpa [hm] using hj)).trans hsle
    const_closed := by
      intro m ρ V
      unfold feedbackResidualSeq
      split
      · simp [EF.denoteWith]
      · simp only [EF.denoteWith, EF.denote_add, EF.denote_mul, EF.denote_const,
          Pi.add_apply, Pi.mul_apply]
        rw [hA.const_closed]
    coefficient_closed := by
      intro z ρ V
      exact hA.coefficient_closed _ ρ V
  }

/-! ## Semantic package -/

/-- The value the sparse sequence takes in a completed world, on either branch: `0` off
schedule, and the determination residual of `A_{f i}` on the active day `f (i+1)`. -/
lemma feedbackResidualSeq_value_eq
    {As : ℕ → AffineCombination} {P : History}
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    {m : ℕ} (hm : feedbackFlag f m = 1) (v : PCWorld) :
    (feedbackResidualSeq As C m).value P v.payout =
      (As (f (feedbackIndex f m))).value P v.payout -
        truth (f (feedbackIndex f m)) := by
  unfold feedbackResidualSeq
  rw [if_neg (by omega)]
  have hsource := sourceIndex_eq_of_flag f hstrict hm
  have heq :
      (⟨EF.add (As (sourceIndex f m)).const
          (EF.mul (EF.const (-1)) (EF.const (C.value (feedbackIndex f m)))),
        (As (sourceIndex f m)).terms⟩ : AffineCombination).value P v.payout =
        (As (sourceIndex f m)).value P v.payout -
          (C.value (feedbackIndex f m) : ℝ) := by
    simp [AffineCombination.value]
    ring
  rw [heq, hsource, C.agrees]

/-- On an active day the source index is at least the tolerance launch index: the deadline
identity `f (i + 1) = m` plus strict monotonicity reflects `m ≥ f (N + 1)` back to
`i ≥ N`, and `f i > i` then puts the *affine* index `f i` past `N` too. -/
lemma le_source_of_flag
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    {N m : ℕ} (hm : feedbackFlag f m = 1) (hmN : f (N + 1) ≤ m) :
    N ≤ f (feedbackIndex f m) := by
  have hdeadline := feedbackFlag_spec f hstrict hm
  have hle : f (N + 1) ≤ f (feedbackIndex f m + 1) := by rw [hdeadline]; exact hmN
  have hN : N ≤ feedbackIndex f m := by
    have := hstrict.le_iff_le.1 hle
    omega
  exact hN.trans (f.lt (feedbackIndex f m)).le

/-- **The sparse feedback sequence's completed-world value vanishes uniformly.**

Only *approximate* determination of `As` is used, with a residual stream tending to zero.
On the active day `f (i+1)` the sequence is `A_{f i}` centred at the computed value of
`truth (f i)`, so a completed world values it at exactly the determination residual at
index `f i` — and `f i → ∞` along the schedule, so the residual is eventually below any
tolerance.  This is what lets the threshold mesh of a LUV combination, which
`def:affthmval` determines only up to its `O(1/n)` mesh error (`dd:mesh`), still supply a
feedback bridge. -/
lemma feedbackResidualSeq_value_vanishing
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth err : ℕ → ℝ} {f : DeferralFunction}
    (hdet : ApproxDeterminedViaTheory As P DP truth err)
    (herr : Tendsto err atTop (𝓝 0))
    (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f) :
    ∀ ε > 0, ∀ᶠ m in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      |(feedbackResidualSeq As C m).value P v.payout| ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 herr ε hε
  rw [Filter.eventually_atTop]
  refine ⟨f (N + 1), fun m hm v hv => ?_⟩
  by_cases hflag : feedbackFlag f m = 0
  · have hzero : (feedbackResidualSeq As C m).value P v.payout = 0 := by
      simp [feedbackResidualSeq, hflag, AffineCombination.value]
    rw [hzero, abs_zero]
    exact hε.le
  · have hm1 : feedbackFlag f m = 1 :=
      (feedbackFlag_zero_or_one f m).resolve_left hflag
    rw [feedbackResidualSeq_value_eq C hstrict hm1 v]
    have hidx : N ≤ f (feedbackIndex f m) :=
      le_source_of_flag f hstrict hm1 hm
    have hsmall := hN _ hidx
    rw [Real.dist_eq, sub_zero] at hsmall
    exact (hdet _ v hv).trans ((le_abs_self _).trans hsmall.le)

/-- The sparse feedback sequence inherits a uniform price bound: off schedule its price is
`0`, and on an active day it is a bounded source price minus a computed value whose
completed-world distance from the source price is bounded by the magnitude and residual. -/
lemma feedbackResidualSeq_bounded
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth err : ℕ → ℝ} {f : DeferralFunction}
    (hpoly : PolySequence As)
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∀ n, (As n).magnitude P ≤ 1)
    (hdet : ApproxDeterminedViaTheory As P DP truth err)
    (herr : Tendsto err atTop (𝓝 0))
    (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    BoundedAffinePrices (feedbackResidualSeq As C) P := by
  obtain ⟨B, hB0, hB⟩ := hbounded
  obtain ⟨v, hv⟩ := exists_consistentWithTheory DP hworld
  obtain ⟨M0, hM0⟩ := herr.bddAbove_range
  set M : ℝ := max M0 0 with hMdef
  have hMerr : ∀ n, err n ≤ M := fun n => (hM0 ⟨n, rfl⟩).trans (le_max_left _ _)
  have hM0le : (0 : ℝ) ≤ M := le_max_right _ _
  refine ⟨2 * B + 1 + M, by positivity, ?_⟩
  intro m n
  unfold feedbackResidualSeq
  by_cases hm : feedbackFlag f m = 0
  · simp [hm, AffineCombination.price, AffineCombination.value]
    linarith
  · have hm1 : feedbackFlag f m = 1 :=
      (feedbackFlag_zero_or_one f m).resolve_left hm
    rw [if_neg hm]
    have hsource := sourceIndex_eq_of_flag f hstrict hm1
    have htruth : |(C.value (feedbackIndex f m) : ℝ)| ≤ B + 1 + M := by
      rw [C.agrees, ← hsource]
      set i := sourceIndex f m with hi
      have hres := hdet i v hv
      have hdiff := (As i).abs_value_sub_price_le_magnitude P v.payout i
        (hpoly.terms_rank i) (by
          intro φ
          rw [PCWorld.payout]
          split <;> norm_num) (hP i)
      have hprice0 := hB i i
      have hmag0 := hmag i
      have hMi := hMerr i
      have hval : |(As i).value P v.payout| ≤ B + 1 := by
        calc
          |(As i).value P v.payout| =
              |((As i).value P v.payout - (As i).price P i) + (As i).price P i| := by ring_nf
          _ ≤ |(As i).value P v.payout - (As i).price P i| +
                |(As i).price P i| := abs_add_le _ _
          _ ≤ B + 1 := by linarith
      rw [abs_le] at hval hres
      rw [abs_le]
      obtain ⟨hv1, hv2⟩ := hval
      obtain ⟨hr1, hr2⟩ := hres
      constructor <;> linarith
    have hprice := hB (sourceIndex f m) n
    have heq :
        (⟨EF.add (As (sourceIndex f m)).const
            (EF.mul (EF.const (-1)) (EF.const (C.value (feedbackIndex f m)))),
          (As (sourceIndex f m)).terms⟩ : AffineCombination).price P n =
          (As (sourceIndex f m)).price P n -
            (C.value (feedbackIndex f m) : ℝ) := by
      simp [AffineCombination.price, AffineCombination.value]
      ring
    rw [heq, abs_le]
    rw [abs_le] at hprice htruth
    constructor <;> linarith

/-- **Public constructor for the `FeedbackTruthSequence` boundary.**
Normalization is deliberately external: `hpoly`, `hbounded`, `hmag`, `hP`, and `hworld`
provide the ordinary paper BCS/market premises, while `C` contains only the delayed
computation.

Determination enters only *approximately*: `hdet` bounds each completed world's
disagreement with the advertised `truth n` by `err n`, and `herr` sends that residual to
zero.  Exact determination is the `err = 0` instance (`feedbackTruthSequence_ofDetermined`).
The slack is what carries the LUV mesh, which `def:affthmval` determines only to within
its `O(1/n)` mesh error (`dd:mesh`).
Paper node: `thm:wubaff` -/
noncomputable def feedbackTruthSequence
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth err : ℕ → ℝ} {f : DeferralFunction}
    (hpoly : PolySequence As)
    (hbounded : BoundedAffinePrices As P)
    (hdet : ApproxDeterminedViaTheory As P DP truth err)
    (herr : Tendsto err atTop (𝓝 0))
    (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    (hmag : ∀ n, (As n).magnitude P ≤ 1)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    FeedbackTruthSequence As truth P DP f := by
  exact {
    determined := ⟨err, herr, hdet⟩
    sequence := feedbackResidualSeq As C
    poly := feedbackResidualSeqPoly hpoly C hstrict
    bounded := feedbackResidualSeq_bounded hpoly hbounded hmag hdet herr C hstrict hP hworld
    magnitude := by
      intro m
      rw [feedbackResidualSeq_magnitude]
      split
      · simp
      · exact hmag _
    value_vanishing := feedbackResidualSeq_value_vanishing hdet herr C hstrict
    feedback_price := by
      intro k
      rw [feedbackResidualSeq_price_at As C hstrict P k, C.agrees]
  }

/-- The exactly-determined instance of `feedbackTruthSequence`, at zero residual.  This is
what the sentence-indicator and affine feedback endpoints use, where `Θ` really does pin
one value per member; only the LUV mesh needs the approximate form.
Paper node: `thm:wubaff` -/
noncomputable def feedbackTruthSequence_ofDetermined
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (hpoly : PolySequence As)
    (hbounded : BoundedAffinePrices As P)
    (hdet : DeterminedViaTheory As P DP truth)
    (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    (hmag : ∀ n, (As n).magnitude P ≤ 1)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    FeedbackTruthSequence As truth P DP f :=
  feedbackTruthSequence hpoly hbounded hdet.approx tendsto_const_nhds C hstrict hmag hP
    hworld

/-! ## Consumers with both feedback boundaries discharged -/

/-- Low-level `thm:wubaff` endpoint: the token emitter and delayed truth sequence are
both constructed, leaving only the paper's operational truth program and ordinary
normalization/market premises.
Paper node: `thm:wubaff` -/
theorem lic_wubaff_ofComputation
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (hdet : DeterminedViaTheory As P DP truth)
    (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    (hsupport : WeightingSupportedOnDeferralImage W P f)
    (hWdiv : DivergentWeighting W P)
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    weightedBias (fun i ↦ (W i).denote P)
      (fun i ↦ (As i).price P i) truth ≈ₙ (fun _ ↦ 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let bridge := feedbackTruthSequence_ofDetermined hpoly hbounded hdet C hstrict hmag hP
    hworld
  exact AffineCombination.lic_wubaff hpoly hW hstrict hsupport
    (FeedbackEmission.feedbackTraderEmissionSigns hpoly hW hstrict)
    bridge hWdiv hmag hworld

/-- `thm:wub`, with both feedback boundaries discharged by the concrete trader emitter and
delayed-truth compiler.  This is the one-share specialization of
`lic_wubaff_ofComputation`; the caller supplies only the paper's sentence sequence,
completed-theory truth stream, weighting, schedule, and deadline-bounded truth program.
Paper node: `thm:wub` -/
theorem lic_wub_ofComputation
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (truth : ℕ → ℝ) (htruth : TheoryTruth φ DP truth)
    (W : ℕ → EF) (hW : PGenerableWeighting W)
    (hWdiv : DivergentWeighting W P)
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (C : FeedbackTruthComputation truth f)
    (hsupport : WeightingSupportedOnDeferralImage W P f)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    weightedBias (fun i ↦ (W i).denote P) (fun i ↦ P i (φ i)) truth ≈ₙ
      (fun _ ↦ 0) := by
  have hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    fun n ψ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n ψ
  have hdet : DeterminedViaTheory (sentenceAffine φ) P DP truth := by
    intro n v hv
    simpa [sentenceAffine, AffineCombination.value] using htruth n v hv
  have h := lic_wubaff_ofComputation (sentenceAffine_polySequence φ hφ) hW hdet C
    hstrict hsupport hWdiv (sentenceAffine_bounded φ P hP)
    (fun i => by simp) hworld
  simpa only [sentenceAffine_price] using h

/-- Paper-facing affine endpoint for an arbitrary BCS.  Its canonical normalization stays
outside `FeedbackTruthComputation`; the supplied program computes the normalized truth
stream that the actual unit-risk trader consumes.
Paper node: `thm:wubaff` -/
theorem boundedCombination_wubaff_ofComputation
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedCombinationSequence As P)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f)
    (C : FeedbackTruthComputation
      (fun n ↦ (h.unitNormalization.scale : ℝ) * truth n) f)
    (hsupport : WeightingSupportedOnDeferralImage W P f)
    (hWdiv : DivergentWeighting W P)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    weightedBias (fun i ↦ (W i).denote P)
      (fun i ↦ (As i).price P i) truth ≈ₙ (fun _ ↦ 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let q : ℚ := h.unitNormalization.scale
  have hdetScaled : DeterminedViaTheory
      (fun n ↦ (As n).scale (.const q)) P DP
      (fun n ↦ (q : ℝ) * truth n) := by
    intro n v hv
    rw [AffineCombination.scale_value, EF.denote_const, hdet n v hv]
  have hboundedScaled : BoundedAffinePrices
      (fun n ↦ (As n).scale (.const q)) P :=
    (h.boundedPrices hP).scaleRat q
  let bridge := feedbackTruthSequence_ofDetermined (h.poly.scaleRat q) hboundedScaled
    hdetScaled C hstrict h.unitNormalization.magnitude_le_one hP hworld
  exact FeedbackEmission.boundedCombination_wubaff_ofFeedbackTruth h hW hdet hstrict
    hsupport bridge hWdiv hworld

/-- **`thm:wubexp` at its corrected premises.**  The threshold mesh, its feedback traders,
and its sparse delayed-truth sequence are all constructed here.

*One premise this endpoint carries is not printed at this node.*  `hsupport`
(`WeightingSupportedOnDeferralImage`: the support of `w` lies in the image of `f`) is
absent from the printed `thm:wubexp` (tex:1822-1832) and appears instead, spuriously, on
`thm:recurringunbiasednessexp` (tex:1812-1820) — whose statement never introduces a
deferral function `f` for it to refer to.  The affine twins settle the intended placement:
`thm:wubaff` (tex:1480-1490) carries the clause and `thm:recurringunbiasedness`
(tex:1225-1233) does not.  The clause belongs on the feedback theorem, so this endpoint
states it here; the mirror half of the same correction is
`BoundedSequence.recurringunbiasednessexp`, which drops it.  Recorded as `PE2` in
`notes/paper-errata.md`.

The semantic premises are the paper's: `hdet` is `def:affthmval` — every completed
world assigns the *combination* `Aₙ` the same value `truth n` — and `hvalued` is the
representation premise that each completed world values the component LUVs somehow
(`W(X)` being a supremum, paper worlds always do).  Neither pins a component LUV's value
across worlds, so `[(1, X), (-1, X)]` for a wholly undetermined `X` is covered.  `C` is
the paper's operational premise: one program emits `thmval` of the mesh by the next
deferral deadline.

*Why the mesh route works under combination-level determination.*  Meshing is nonlinear
(each LUV is replaced by a rounded threshold bundle), so the precision-`n` mesh of a
combination-determined sequence is **not** determined: two completed worlds may split the
determined total differently across components and mesh to different values.  What
`lem:conluvapprox` gives is quantitative — each world's mesh value is within
`shareNorm/n` of the determined value, hence any two agree to within twice that
(`WorldValued.normalizedMesh_approxDetermined`), a residual that vanishes
(`meshErrorBound_tendsto_zero`).  Affine provability induction needs no more than that:
`affine_provind_theory_tendsto_zero` learns the price of a sequence whose completed-world
values merely tend to zero uniformly.  So the feedback bridge is built at
`ApproxDeterminedViaTheory`, not `DeterminedViaTheory`.

No endpoint of this node uses `LUVCombination.ExactTheoryPresentation`, and none should:
that structure fixes a completed-theory value for *every component LUV*, which is strictly
stronger than `def:affthmval` and would be a premise the paper does not state.

Kind `C`; provenance: `hdet`, `hvalued`, `hshare`, `hW`, `hWdiv`, `hstrict` (a) — the
paper's own hypotheses; `hsupport` (a) — the paper's own hypothesis, at the node it was
transposed away from (`PE2`); `C` (a) — the paper's deadline-bounded truth program, in the
`dd:fuel` efficiency model, asked for the normalized mesh rather than for the combination
itself (see the mesh paragraph above and `dd:mesh`); `hworld` (a) — finite-stage plausible
worlds.
Paper node: `thm:wubexp` -/
theorem luv_wubexp_ofComputation
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (hvalued : LUVCombination.WorldValued As DP)
    {truth : ℕ → ℝ} (hdet : LUVCombination.DeterminedViaTheory As P DP truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    (hWdiv : DivergentWeighting W P)
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (C : FeedbackTruthComputation
      (LUVCombination.normalizedMeshTruth As P DP hworld b) f)
    (hsupport : WeightingSupportedOnDeferralImage W P f) :
    weightedBias (fun i ↦ (W i).denote P)
      (fun i ↦ (As i).expect P i) truth ≈ₙ (fun _ ↦ 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  have hmeshDet : AffineCombination.ApproxDeterminedViaTheory
      (LUVCombination.normalizedMesh As b) P DP
      (LUVCombination.normalizedMeshTruth As P DP hworld b)
      (LUVCombination.meshErrorBound As P b) :=
    hvalued.normalizedMesh_approxDetermined hdet hworld b
  have herr : Tendsto (LUVCombination.meshErrorBound As P b) atTop (𝓝 0) :=
    LUVCombination.meshErrorBound_tendsto_zero b hshare
  let bridge := feedbackTruthSequence (h.normalizedMesh_poly b)
    (h.normalizedMesh_boundedPrices b hP) hmeshDet herr C hstrict
    (LUVCombination.normalizedMesh_magnitude_le_one b hshare) hP hworld
  exact FeedbackEmission.luv_wubexp_ofFeedbackTruth h hvalued hdet b hshare
    hW hWdiv hstrict hsupport hworld bridge

end FeedbackTruth
end LogicalInduction
