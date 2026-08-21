import LogicalInduction.Construction.Witnesses.SemanticPrime
import LogicalInduction.Construction.Witnesses.ProductDefinition

/-!
# The unrestricted semantic-source obstruction

`LUV.RpnThresholdCodeSeq` controls how efficiently threshold sentences are emitted, but
does not restrict which propositional atoms those sentences contain.  Consequently an
efficient source can diagonalize against every tag-`0` semantic-source schema.  This file
records the obstruction: no non-vacuous fixed process can wrap every such source in a
`PresentedLUVSeq` while identifying the wrapper's thresholds with the original thresholds
in all completed worlds.

This is a representation-boundary result, not a parser limitation.  In particular,
`RpnSentenceCodes.primrec` and `RpnSentenceCodes.exists_code` already provide the canonical
total sentence emitter required downstream.
-/

namespace LogicalInduction

open LO LO.Propositional

private lemma natPair_zero_zero : Nat.pair 0 0 = 0 := by rfl

private lemma encodeRat_zero : Encodable.encode (0 : ℚ) = Nat.pair 0 1 := by rfl

attribute [local irreducible] Nat.sqrt

/-! ## What the existing certificate does provide -/

/-- A canonical total naming program can be selected directly from the existing
`RpnThresholdCodeSeq` certificate.  No extra named-code premise is needed. -/
noncomputable def rpnThresholdSourceCode {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) : Nat.Partrec.Code :=
  Classical.choose hX.exists_code

/-- Exact specification of the selected naming program on the certificate's packed
`⟨n,⟨k,i⟩⟩` inputs. -/
lemma rpnThresholdSourceCode_spec {X : ℕ → LUV}
    (hX : LUV.RpnThresholdCodeSeq X) (m : ℕ) :
    Encodable.encode ((X m.unpair.1).gt
      ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ))) ∈
      (rpnThresholdSourceCode hX).eval m :=
  Classical.choose_spec hX.exists_code m

/-! ## The local base-language separation invariant -/

/-- A sentence belongs to the pre-extension source vocabulary when none of its atoms use
the semantic-prime tag reserved for the extension. -/
def SemanticPrimeFreshSentence (φ : Sentence) : Prop :=
  ∀ a ∈ sentenceAtomCodes φ, a.unpair.1 ≠ semanticPrimeTag

/-- Pointwise source-language separation for a sequence of LUV threshold families. -/
def SemanticPrimeFreshLUVSeq (X : ℕ → LUV) : Prop :=
  ∀ n r, SemanticPrimeFreshSentence ((X n).gt r)

/-- At index `n`, negate the semantic leaf belonging to the `n`th source schema.  Whichever
tag-`0` schema a proposed presentation chooses, the source attacks it at one index. -/
def semanticDiagonalLUVSeq (n : ℕ) : LUV where
  gt r := ∼semanticPrimeSentence (semanticSourceSchema n)
    (Nat.pair n (Encodable.encode r))

@[simp] lemma semanticDiagonalLUVSeq_gt (n : ℕ) (r : ℚ) :
    (semanticDiagonalLUVSeq n).gt r =
      ∼semanticPrimeSentence (semanticSourceSchema n)
        (Nat.pair n (Encodable.encode r)) := rfl

/-- The diagonal family is already efficiently codeable in the stronger whole-value
interface.  Thus it is not excluded by the paper-facing `RpnThresholdCodeSeq` premise. -/
lemma semanticDiagonalLUVSeq_polyThresholdCodeSeq :
    LUV.PolyThresholdCodeSeq semanticDiagonalLUVSeq := by
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
  have schemaPF := (PolyFueled.const 0).pair hn
  have atomPF := ((PolyFueled.const 1).pair
    ((PolyFueled.const semanticPrimeTag).pair
      (schemaPF.pair (hn.pair meshPF)))).succ_comp
  have negPF := ((PolyFueled.const 2).pair
    (atomPF.pair (PolyFueled.const 1))).succ_comp
  refine ⟨_, negPF.of_eq (fun m => ?_)⟩
  rw [semanticDiagonalLUVSeq_gt, semanticPrimeSentence, semanticPrimeCode,
    semanticSourceSchema, encode_negAtom]
  simp only [Nat.unpair_pair, ifzSelFn]
  have hpair00 : Nat.pair 0 0 = 0 := natPair_zero_zero
  rw [hpair00]
  by_cases hk0 : m.unpair.2.unpair.1 = 0
  · rw [if_pos hk0, hk0]
    have hrat0 : Encodable.encode (0 : ℚ) = Nat.pair 0 1 := encodeRat_zero
    simp [hrat0]
  · rw [if_neg hk0]
    have hg : 0 < Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hk0)
    have hg1 : (Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1).pred + 1 =
        Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.succ_pred_eq_of_pos hg
    rw [hg1, encode_rat_natCast_div hk0, two_mul]

/-- The same diagonal family satisfies the exact source premise proposed for
`presented_of_rpn`. -/
lemma semanticDiagonalLUVSeq_rpnThresholdCodeSeq :
    LUV.RpnThresholdCodeSeq semanticDiagonalLUVSeq :=
  LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq
    semanticDiagonalLUVSeq_polyThresholdCodeSeq

/-- No completed world can validate threshold reflection between the diagonal source and
any `PresentedLUVSeq`.  The contradiction occurs at the presentation's own schema index. -/
theorem semanticDiagonal_not_reflected (DP : DeductiveProcess) (Xhat : PresentedLUVSeq) :
    ¬ (∃ v : PCWorld, v.ConsistentWithTheory DP ∧
      ∀ n r,
        (v.Holds ((Xhat.toLUV n).gt r) ↔
          v.Holds ((semanticDiagonalLUVSeq n).gt r))) := by
  rintro ⟨v, hv, hreflect⟩
  let n := Xhat.thresholdSchema.unpair.2
  have hschema : semanticSourceSchema n = Xhat.thresholdSchema := by
    rw [semanticSourceSchema]
    exact (congrArg (fun k => Nat.pair k Xhat.thresholdSchema.unpair.2)
      Xhat.source_schema).symm.trans (Nat.pair_unpair Xhat.thresholdSchema)
  have h := hreflect n 0
  rw [PresentedLUVSeq.gt_eq, semanticDiagonalLUVSeq_gt, hschema, holds_not] at h
  by_cases hp : v.Holds
      (semanticPrimeSentence Xhat.thresholdSchema
        (Nat.pair n (Encodable.encode (0 : ℚ))))
  · exact (h.mp hp) hp
  · exact hp (h.mpr hp)

/-- Therefore an unrestricted, fixed-process `presented_of_rpn` theorem plus non-vacuity
is inconsistent.  Any successful bridge must restore the paper's language-separation fact
(for example as a type-level source-language invariant); parser computability alone cannot
prove it from `RpnThresholdCodeSeq`. -/
theorem no_nonvacuous_universal_presented_of_rpn (DP : DeductiveProcess)
    (presented_of_rpn : ∀ (X : ℕ → LUV), LUV.RpnThresholdCodeSeq X →
      ∃ Xhat : PresentedLUVSeq,
        ∀ n r (v : PCWorld), v.ConsistentWithTheory DP →
          (v.Holds ((Xhat.toLUV n).gt r) ↔ v.Holds ((X n).gt r))) :
    ¬ ∃ v : PCWorld, v.ConsistentWithTheory DP := by
  rintro ⟨v, hv⟩
  obtain ⟨Xhat, hreflect⟩ := presented_of_rpn semanticDiagonalLUVSeq
    semanticDiagonalLUVSeq_rpnThresholdCodeSeq
  exact semanticDiagonal_not_reflected DP Xhat
    ⟨v, hv, fun n r => hreflect n r v hv⟩

/-! ## The obstruction inside the world-valued CCEE source class -/

/-- The distinguished proposition attacked by the valued diagonal at index `n`. -/
def semanticValuedDiagonalProp (n : ℕ) : Sentence :=
  semanticPrimeSentence (semanticSourceSchema n)
    (Nat.pair n (Encodable.encode (0 : ℚ)))

/-- A genuine indicator-style `[0,1]` LUV: it has value `1` when the distinguished
semantic proposition is false and value `0` when it is true. -/
def semanticValuedDiagonalLUVSeq (n : ℕ) : LUV where
  gt r := if r < 0 then ⊤ else if r < 1 then ∼semanticValuedDiagonalProp n else ⊥

@[simp] lemma semanticValuedDiagonalLUVSeq_gt (n : ℕ) (r : ℚ) :
    (semanticValuedDiagonalLUVSeq n).gt r =
      (if r < 0 then ⊤ else if r < 1 then ∼semanticValuedDiagonalProp n else ⊥) := rfl

/-- The valued diagonal is an indicator in every deductive process, without using
consistency: its threshold cut is definitionally coherent. -/
lemma semanticValuedDiagonalLUVSeq_isIndicator (DP : DeductiveProcess) (n : ℕ) :
    (semanticValuedDiagonalLUVSeq n).IsIndicator
      (∼semanticValuedDiagonalProp n) DP := by
  intro v hv r
  have hr0 : ((r : ℝ) < 0) ↔ r < 0 := by exact_mod_cast Iff.rfl
  have hr1 : ((r : ℝ) < 1) ↔ r < 1 := by exact_mod_cast Iff.rfl
  refine ⟨fun h => ?_, fun hlo hhi => ?_, fun h => ?_⟩
  · rw [semanticValuedDiagonalLUVSeq_gt, if_pos (hr0.mp h)]
    exact PCWorld.holds_top v
  · have hn0 : ¬ r < 0 := fun h => (not_lt.mpr hlo) (hr0.mpr h)
    rw [semanticValuedDiagonalLUVSeq_gt, if_neg hn0, if_pos (hr1.mp hhi)]
  · have hn1 : ¬ r < 1 := fun h' => (not_lt.mpr h) (hr1.mpr h')
    have hn0 : ¬ r < 0 := fun h' => hn1 (h'.trans (by norm_num))
    simp [semanticValuedDiagonalLUVSeq_gt, hn0, hn1, PCWorld.Holds,
      LO.Propositional.Formula.Boolean.val]

/-- Hence the valued diagonal satisfies the closed CCEE `source_valued` premise for every
process, at the Boolean value of its defining indicator proposition. -/
theorem semanticValuedDiagonalLUVSeq_valuesAt (DP : DeductiveProcess) (n : ℕ)
    (v : PCWorld) (hv : v.ConsistentWithTheory DP) :
    v.ValuesAt (semanticValuedDiagonalLUVSeq n)
      (v.payout (∼semanticValuedDiagonalProp n)) :=
  (semanticValuedDiagonalLUVSeq_isIndicator DP n).valuesAt hv

theorem semanticValuedDiagonalLUVSeq_source_valued (DP : DeductiveProcess) :
    ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ∃ x, v.ValuesAt (semanticValuedDiagonalLUVSeq n) x := by
  intro n v hv
  exact ⟨v.payout (∼semanticValuedDiagonalProp n),
    semanticValuedDiagonalLUVSeq_valuesAt DP n v hv⟩

private lemma semanticValuedDiagonalProp_neg_rpn :
    RpnSentenceCodes (fun m => ∼semanticValuedDiagonalProp m.unpair.1) := by
  have hn := PolyFueled.left
  have hschema := (PolyFueled.const 0).pair hn
  have hinput := hn.pair (PolyFueled.const (Encodable.encode (0 : ℚ)))
  have hatom := ((PolyFueled.const 1).pair
    ((PolyFueled.const semanticPrimeTag).pair (hschema.pair hinput))).succ_comp
  have hneg := ((PolyFueled.const 2).pair
    (hatom.pair (PolyFueled.const 1))).succ_comp
  refine RpnSentenceCodes.ofPolySentenceCodes ⟨_, hneg.of_eq (fun m => ?_)⟩
  simp only [semanticValuedDiagonalProp, semanticPrimeSentence, semanticPrimeCode,
    semanticSourceSchema, encode_negAtom]
  have hpair00 : Nat.pair 0 0 = 0 := natPair_zero_zero
  simp [hpair00]

/-- On a mesh query `⟨n,⟨k,i⟩⟩`, this selector is zero exactly when `i/k < 1`, including
the repository's `k = 0` convention where the rational quotient is zero. -/
def semanticValuedDiagonalMeshSelector (m : ℕ) : ℕ :=
  ifzSelFn (Nat.pair 0 (m.unpair.2.unpair.2 + 1 - m.unpair.2.unpair.1))
    m.unpair.2.unpair.1

lemma semanticValuedDiagonalMeshSelector_polyFueled :
    ∃ c, PolyFueled c semanticValuedDiagonalMeshSelector := by
  have hk := PolyFueled.left.comp PolyFueled.right
  have hi := PolyFueled.right.comp PolyFueled.right
  have htest := subc_polyFueled.comp (hi.succ_comp.pair hk)
  refine ⟨_, (ifzSel_polyFueled.comp (((PolyFueled.const 0).pair htest).pair hk)).of_eq
    (fun m => by simp only [semanticValuedDiagonalMeshSelector, Nat.unpair_pair])⟩

/-- The world-valued diagonal remains efficiently codeable. -/
lemma semanticValuedDiagonalLUVSeq_rpnThresholdCodeSeq :
    LUV.RpnThresholdCodeSeq semanticValuedDiagonalLUVSeq := by
  obtain ⟨c, hc⟩ := semanticValuedDiagonalMeshSelector_polyFueled
  have h := RpnSentenceCodes.ifZero semanticValuedDiagonalProp_neg_rpn
    (RpnSentenceCodes.const (⊥ : Sentence)) hc
  refine h.of_eq (fun m => ?_)
  rw [semanticValuedDiagonalLUVSeq_gt]
  have hnonneg : ¬ ((m.unpair.2.unpair.2 : ℚ) /
      (m.unpair.2.unpair.1 : ℚ)) < 0 :=
    not_lt.mpr (div_nonneg (by positivity) (by positivity))
  rw [if_neg hnonneg]
  by_cases hk0 : m.unpair.2.unpair.1 = 0
  · simp [semanticValuedDiagonalMeshSelector, hk0, ifzSelFn]
  · by_cases hi : m.unpair.2.unpair.2 < m.unpair.2.unpair.1
    · have hsub : m.unpair.2.unpair.2 + 1 - m.unpair.2.unpair.1 = 0 := by omega
      have hrat : (m.unpair.2.unpair.2 : ℚ) /
          (m.unpair.2.unpair.1 : ℚ) < 1 := by
        rw [div_lt_one (by exact_mod_cast Nat.pos_of_ne_zero hk0)]
        exact_mod_cast hi
      simp [semanticValuedDiagonalMeshSelector, hk0, hsub, hrat, ifzSelFn]
    · have hsub : 0 < m.unpair.2.unpair.2 + 1 - m.unpair.2.unpair.1 := by omega
      have hrat : ¬ (m.unpair.2.unpair.2 : ℚ) /
          (m.unpair.2.unpair.1 : ℚ) < 1 := by
        rw [not_lt, one_le_div (by exact_mod_cast Nat.pos_of_ne_zero hk0)]
        exact_mod_cast (Nat.le_of_not_gt hi)
      simp [semanticValuedDiagonalMeshSelector, hk0, hsub.ne', hrat, ifzSelFn]

/-- Even inside the actual world-valued e.c. source class used by closed CCEE, no
presentation can reflect this source in a completed world. -/
theorem semanticValuedDiagonal_not_reflected (DP : DeductiveProcess)
    (Xhat : PresentedLUVSeq) :
    ¬ (∃ v : PCWorld, v.ConsistentWithTheory DP ∧
      ∀ n r, v.Holds ((Xhat.toLUV n).gt r) ↔
        v.Holds ((semanticValuedDiagonalLUVSeq n).gt r)) := by
  rintro ⟨v, hv, hreflect⟩
  let n := Xhat.thresholdSchema.unpair.2
  have hschema : semanticSourceSchema n = Xhat.thresholdSchema := by
    rw [semanticSourceSchema]
    exact (congrArg (fun k => Nat.pair k Xhat.thresholdSchema.unpair.2)
      Xhat.source_schema).symm.trans (Nat.pair_unpair Xhat.thresholdSchema)
  have h := hreflect n 0
  rw [PresentedLUVSeq.gt_eq, semanticValuedDiagonalLUVSeq_gt, if_neg (by norm_num),
    if_pos (by norm_num), semanticValuedDiagonalProp, hschema, holds_not] at h
  by_cases hp : v.Holds (semanticPrimeSentence Xhat.thresholdSchema
      (Nat.pair n (Encodable.encode (0 : ℚ))))
  · exact (h.mp hp) hp
  · exact hp (h.mpr hp)

/-- Strengthened obstruction: even restricting the universal bridge to source families
that satisfy the exact completed-world valuedness premise of closed CCEE is incompatible
with a non-vacuous fixed process. -/
theorem no_nonvacuous_worldValued_presented_of_rpn (DP : DeductiveProcess)
    (presented_of_rpn : ∀ (X : ℕ → LUV), LUV.RpnThresholdCodeSeq X →
      (∀ n (v : PCWorld), v.ConsistentWithTheory DP → ∃ x, v.ValuesAt (X n) x) →
      ∃ Xhat : PresentedLUVSeq,
        ∀ n r (v : PCWorld), v.ConsistentWithTheory DP →
          (v.Holds ((Xhat.toLUV n).gt r) ↔ v.Holds ((X n).gt r))) :
    ¬ ∃ v : PCWorld, v.ConsistentWithTheory DP := by
  rintro ⟨v, hv⟩
  obtain ⟨Xhat, hreflect⟩ := presented_of_rpn semanticValuedDiagonalLUVSeq
    semanticValuedDiagonalLUVSeq_rpnThresholdCodeSeq
    (semanticValuedDiagonalLUVSeq_source_valued DP)
  exact semanticValuedDiagonal_not_reflected DP Xhat
    ⟨v, hv, fun n r => hreflect n r v hv⟩

#print axioms semanticValuedDiagonalLUVSeq_rpnThresholdCodeSeq
#print axioms semanticValuedDiagonalLUVSeq_source_valued
#print axioms no_nonvacuous_worldValued_presented_of_rpn

end LogicalInduction
