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
  have hpair00 : Nat.pair 0 0 = 0 := by native_decide
  rw [hpair00]
  by_cases hk0 : m.unpair.2.unpair.1 = 0
  · rw [if_pos hk0, hk0]
    have hrat0 : Encodable.encode (0 : ℚ) = Nat.pair 0 1 := by native_decide
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

end LogicalInduction
