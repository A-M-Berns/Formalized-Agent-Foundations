import LogicalInduction.Construction.Witnesses.SemanticJoint

/-!
# Proof-carrying source LUVs: the semantic certificate boundary

The paper's first-order definition of a `[0,1]` LUV supplies more than efficient threshold
emission: in every completed theory world its rational thresholds form a bounded downward
cut.  `RationalCutAt` isolates exactly that semantic payload at the existing propositional
ABI.  The theorem `RationalCutAt.exists_valuesAt` proves that this payload is sufficient to
recover the repository's `PCWorld.ValuesAt` interface, including genuinely undecided cuts.

This is deliberately only the soundness kernel for the future encoded certificate registry.
A caller-supplied proof of `RationalCutAt` is not by itself an acceptable fixed-process
certificate: the deductive process cannot inspect an arbitrary Lean proof chosen after the
process.  The registry must carry checkable object-level evidence that makes these three
clauses hold in every completed base-theory world.
-/

namespace LogicalInduction

open Set

/-- The completed-world content of a genuine paper `[0,1]` LUV.

Thresholds below zero hold, thresholds above one fail, and truth is downward closed.  No
decidability at the represented value is required; this deliberately permits the paper's
nonstandard/undecided boundary behavior. -/
structure PCWorld.RationalCutAt (v : PCWorld) (X : LUV) : Prop where
  below_zero : ∀ r : ℚ, (r : ℝ) < 0 → v.Holds (X.gt r)
  above_one : ∀ r : ℚ, 1 < (r : ℝ) → ¬v.Holds (X.gt r)
  downward : ∀ r s : ℚ, r < s → v.Holds (X.gt s) → v.Holds (X.gt r)

namespace PCWorld.RationalCutAt

variable {v : PCWorld} {X : LUV}

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

/-- A bounded downward rational cut determines a unique repository LUV value. -/
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

/-- The represented value is canonical, even though truth at a threshold equal to the value
may remain undecided. -/
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

/-! ## Executable cut certificates

The following certificate is intentionally code-bearing.  `stageCode` is a repository
program which, for each requested cut law, returns a stage of the already-fixed base
deductive process containing that law.  A universal source registry can run this code and
check finite-stage membership; it need not inspect the accompanying Lean correctness proof.
-/

/-- Packed certificate query for the lower-bound law at source index `n`, threshold `r`. -/
def sourceCutBelowJob (n : ℕ) (r : ℚ) : ℕ :=
  Nat.pair 0 (Nat.pair n (Encodable.encode r))

/-- Packed certificate query for the upper-bound law at source index `n`, threshold `r`. -/
def sourceCutAboveJob (n : ℕ) (r : ℚ) : ℕ :=
  Nat.pair 1 (Nat.pair n (Encodable.encode r))

/-- Packed certificate query for downward closure from `s` to `r`. -/
def sourceCutDownwardJob (n : ℕ) (r s : ℚ) : ℕ :=
  Nat.pair 2 (Nat.pair n (Nat.pair (Encodable.encode r) (Encodable.encode s)))

/-- Object-level evidence that the base process proves all rational-cut laws for `X`.

The returned stage is executable data.  The three soundness fields are metatheoretic
verification of that data, analogous to the `code_spec` field of the repository's other
certified computations. -/
structure SourceCutCertificate (DP : DeductiveProcess) (X : ℕ → LUV) where
  stageCode : Nat.Partrec.Code
  below : ∀ (n : ℕ) (r : ℚ), (r : ℝ) < 0 →
    ∃ k, k ∈ stageCode.eval (sourceCutBelowJob n r) ∧ (X n).gt r ∈ DP.D k
  above : ∀ (n : ℕ) (r : ℚ), 1 < (r : ℝ) →
    ∃ k, k ∈ stageCode.eval (sourceCutAboveJob n r) ∧ (∼(X n).gt r) ∈ DP.D k
  downward : ∀ (n : ℕ) (r s : ℚ), r < s →
    ∃ k, k ∈ stageCode.eval (sourceCutDownwardJob n r s) ∧
      ((X n).gt s 🡒 (X n).gt r) ∈ DP.D k

namespace SourceCutCertificate

variable {DP : DeductiveProcess} {X : ℕ → LUV}

/-- A checked executable certificate makes every completed base-theory world see a bounded
downward cut. -/
lemma rationalCutAt (C : SourceCutCertificate DP X) {v : PCWorld}
    (hv : v.ConsistentWithTheory DP) (n : ℕ) : v.RationalCutAt (X n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨k, _, hk⟩ := C.below n r hr
    exact hv k _ hk
  · intro r hr
    obtain ⟨k, _, hk⟩ := C.above n r hr
    exact (holds_not v _).mp (hv k _ hk)
  · intro r s hrs hs
    obtain ⟨k, _, hk⟩ := C.downward n r s hrs
    exact (hv k _ hk) hs

/-- Consequently executable cut certification discharges the actual `source_valued`
premise used by closed CCEE. -/
lemma valuesAt (C : SourceCutCertificate DP X) {v : PCWorld}
    (hv : v.ConsistentWithTheory DP) (n : ℕ) : ∃ x : ℝ, v.ValuesAt (X n) x :=
  (C.rationalCutAt hv n).exists_valuesAt

end SourceCutCertificate

/-- The local paper-facing source representation at the current propositional ABI.

It retains efficient emission, carries the executable cut proof program, and records
pre-extension vocabulary ownership.  The latter is a theorem about the emitted syntax;
the universal registry must enforce it by decoding the emitter output before activation.
Unlike `PresentedLUVSeq`, this object does not assume semantic-prime reflection. -/
structure CertifiedSourceLUVSeq (DP : DeductiveProcess) where
  toLUV : ℕ → LUV
  threshold_codes : LUV.RpnThresholdCodeSeq toLUV
  /-- Total compiler for arbitrary rational threshold queries.  The paper supplies this by
  syntactically substituting the rational into the e.c.-emitted one-variable LUV formula;
  `RpnThresholdCodeSeq` separately certifies polynomial emission on the expectation grids. -/
  emitterCode : Nat.Partrec.Code
  emitter_spec : ∀ (n : ℕ) (r : ℚ),
    Encodable.encode ((toLUV n).gt r) ∈
      emitterCode.eval (Nat.pair n (Encodable.encode r))
  old_language : SemanticPrimeFreshLUVSeq toLUV
  cut_certificate : SourceCutCertificate DP toLUV

namespace CertifiedSourceLUVSeq

variable {DP : DeductiveProcess}

/-- The faithful source object internally supplies completed-world valuedness. -/
lemma source_valued (X : CertifiedSourceLUVSeq DP) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory DP) : ∃ x : ℝ, v.ValuesAt (X.toLUV n) x :=
  X.cut_certificate.valuesAt hv n

/-- Compact source handles at a fixed schema. -/
def semanticHandleLUVSeq (schema n : ℕ) : LUV where
  gt r := semanticPrimeSentence schema (Nat.pair n (Encodable.encode r))

@[simp] lemma semanticHandleLUVSeq_gt (schema n : ℕ) (r : ℚ) :
    (semanticHandleLUVSeq schema n).gt r =
      semanticPrimeSentence schema (Nat.pair n (Encodable.encode r)) := rfl

/-- A semantic handle family has a stronger whole-value threshold certificate.  The source
formula remains behind the handle; only the rational query is normalized here. -/
lemma semanticHandleLUVSeq_polyThresholdCodeSeq (schema : ℕ) :
    LUV.PolyThresholdCodeSeq (semanticHandleLUVSeq schema) := by
  obtain ⟨cg, hgcd⟩ := gcdc_polyFueled
  obtain ⟨cdm, hdm⟩ := divmod1_polyFueled
  obtain ⟨cad, had⟩ := addc_polyFueled
  have hn := PolyFueled.left
  have hk := PolyFueled.left.comp PolyFueled.right
  have hi := PolyFueled.right.comp PolyFueled.right
  have gPF := hgcd.comp (hi.pair hk)
  have pgPF := predc_polyFueled.comp gPF
  have numPF := PolyFueled.left.comp (hdm.comp (pgPF.pair hi))
  have denPF := PolyFueled.left.comp (hdm.comp (pgPF.pair hk))
  have h2num := had.comp (numPF.pair numPF)
  have meshPF := ifzSel_polyFueled.comp
    (((PolyFueled.const (Nat.pair 0 1)).pair (h2num.pair denPF)).pair hk)
  have fullPF := ((PolyFueled.const 1).pair
    ((PolyFueled.const semanticPrimeTag).pair
      ((PolyFueled.const schema).pair (hn.pair meshPF)))).succ_comp
  refine ⟨_, fullPF.of_eq (fun m => ?_)⟩
  rw [semanticHandleLUVSeq_gt, semanticPrimeSentence, semanticPrimeCode, encode_atom]
  simp only [Nat.unpair_pair, ifzSelFn]
  by_cases hk0 : m.unpair.2.unpair.1 = 0
  · rw [if_pos hk0, hk0]
    norm_num
    rfl
  · rw [if_neg hk0]
    have hg : 0 < Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hk0)
    have hg1 : (Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1).pred + 1 =
        Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.succ_pred_eq_of_pos hg
    rw [hg1, encode_rat_natCast_div hk0, two_mul]

lemma semanticHandleLUVSeq_rpnThresholdCodeSeq (schema : ℕ) :
    LUV.RpnThresholdCodeSeq (semanticHandleLUVSeq schema) :=
  LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq
    (semanticHandleLUVSeq_polyThresholdCodeSeq schema)

/-- The self-describing source schema stores both executable programs: efficient threshold
emission and cut-certificate stage lookup. -/
noncomputable def thresholdSchema (X : CertifiedSourceLUVSeq DP) : ℕ :=
  semanticEmitterSchema (Nat.pair
    (Encodable.encode X.emitterCode)
    (Encodable.encode X.cut_certificate.stageCode))

@[simp] lemma thresholdSchema_source (X : CertifiedSourceLUVSeq DP) :
    X.thresholdSchema.unpair.1 = 0 := by
  simp [thresholdSchema]

/-- Canonical compact wrapper.  Reflection is intentionally not claimed here: that is the
remaining universal verifier/process construction. -/
noncomputable def toPresented (X : CertifiedSourceLUVSeq DP) : PresentedLUVSeq where
  thresholdSchema := X.thresholdSchema
  source_schema := X.thresholdSchema_source
  toLUV := semanticHandleLUVSeq X.thresholdSchema
  threshold_codes := semanticHandleLUVSeq_rpnThresholdCodeSeq X.thresholdSchema
  threshold_named := fun _ _ => rfl

@[simp] lemma toPresented_gt (X : CertifiedSourceLUVSeq DP) (n : ℕ) (r : ℚ) :
    ((X.toPresented.toLUV n).gt r) =
      semanticPrimeSentence X.thresholdSchema (Nat.pair n (Encodable.encode r)) := rfl

end CertifiedSourceLUVSeq

/-! ## Negative admission test -/

/-- The malformed fresh increasing family cannot carry an executable cut certificate for
any non-vacuous base process.  This is the registry-level rejection counterpart of
`semanticFreshIncreasing_not_jointly_reflected`. -/
lemma semanticFreshIncreasing_no_cutCertificate (DP : DeductiveProcess)
    (hworld : ∃ v : PCWorld, v.ConsistentWithTheory DP) :
    SourceCutCertificate DP semanticFreshIncreasingLUVSeq → False := by
  intro C
  obtain ⟨v, hv⟩ := hworld
  have hcut := C.rationalCutAt hv 0
  have hone : v.Holds ((semanticFreshIncreasingLUVSeq 0).gt 1) := by
    simp [semanticFreshIncreasingLUVSeq_gt, PCWorld.Holds,
      LO.Propositional.Formula.Boolean.val]
  have hzero := hcut.downward 0 1 (by norm_num) hone
  simpa [semanticFreshIncreasingLUVSeq_gt, PCWorld.Holds,
    LO.Propositional.Formula.Boolean.val] using hzero

#print axioms PCWorld.RationalCutAt.exists_valuesAt
#print axioms PCWorld.RationalCutAt.valuesAt_iff_sSup
#print axioms SourceCutCertificate.rationalCutAt
#print axioms SourceCutCertificate.valuesAt
#print axioms CertifiedSourceLUVSeq.source_valued
#print axioms CertifiedSourceLUVSeq.semanticHandleLUVSeq_rpnThresholdCodeSeq
#print axioms CertifiedSourceLUVSeq.toPresented
#print axioms semanticFreshIncreasing_no_cutCertificate

end LogicalInduction
