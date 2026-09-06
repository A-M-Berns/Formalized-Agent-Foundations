import LogicalInduction.Properties.UniformNonDogmatism
import LogicalInduction.Framework.Emission.Emission
import LogicalInduction.Framework.Emission.WriteOut

/-!
# Efficient repeated enumeration

`Properties/UniformNonDogmatism.lean` states `thm:obu` over an
`EfficientRepeatedEnumeration`: a `def:ec` stream in which every member of the source recurs
arbitrarily late.  The paper builds one inside its own proof (tex:5651-5656) by padding and
repeating; this module carries out that step, twice.

* `triangularRepeat` and `EfficientRepeatedEnumeration.ofBig` — the exact witness when the
  source is already a write-out-metered sentence stream (`BigSentenceCodes`).  The second
  pairing coordinate is pure padding, so every source index recurs arbitrarily late and the
  reindexing is poly-fueled.
* `CEEnumeration` and `EfficientRepeatedEnumeration.ofCE` — the paper's own premise: an
  arbitrary computably enumerable source, with no clock.  The bounded universal interpreter
  `codeEvalnNat` (poly-fueled by `codeEvalnNat_polyFueled`) dovetails it — on `⟨i, fuel⟩`,
  run the enumerator on `i` for `fuel` steps and emit the decoded output — so the emitted
  stream is polynomial however expensive the source is.

Two deviations from the paper's prose, both forced and both narrowing nothing: the dovetail
runs under the interpreter clock rather than being left informal, and the padding element is
`source 0` rather than the paper's `⊤`, because `EfficientRepeatedEnumeration.sound` requires
padding from the source's own range.

`lic_uniform_nonDogmatism_ofCE` is the resulting endpoint: `thm:obu` at the paper's own c.e.
premise, over an arbitrary inductor.
-/

namespace LogicalInduction

/-- Triangular repetition of an already polynomial sentence stream.  The second pairing
coordinate is pure padding, so every source index occurs arbitrarily late. -/
def triangularRepeat (source : ℕ → Sentence) (n : ℕ) : Sentence :=
  source n.unpair.1

lemma triangularRepeat_repeats (source : ℕ → Sentence) :
    RepeatsEveryMember (triangularRepeat source) := by
  intro i N
  refine ⟨Nat.pair i.unpair.1 N, Nat.right_le_pair _ _, ?_⟩
  simp [triangularRepeat]

/-- The exact efficient-repetition witness when the supplied enumeration is already an
𝓔𝓒 (`def:ec`, write-out metered) sentence stream.  The second pairing coordinate is pure
padding, so every source index recurs arbitrarily late, and the reindexing is poly-fueled.
The bounded universal-emulator extension below removes this stronger clock assumption for
arbitrary computable/c.e. source programs.
Paper node: `def:ec` -/
def EfficientRepeatedEnumeration.ofBig (source : ℕ → Sentence)
    (hsource : BigSentenceCodes source) :
    EfficientRepeatedEnumeration source where
  sequence := triangularRepeat source
  sequence_poly := hsource.comp PolyFueled.left
  repeats := triangularRepeat_repeats source
  sound j := ⟨j.unpair.1, rfl⟩
  covers i := ⟨Nat.pair i 0, by simp [triangularRepeat]⟩

/-! ### General (c.e.) efficient repetition via the universal simulator

`ofBig` requires the source stream to already be efficiently codeable.  The paper's Uniform
Non-Dogmatism preprocesses an arbitrary **c.e.** stream, which need not be poly.  The
bounded universal interpreter `codeEvalnNat` — itself poly-fueled by
`codeEvalnNat_polyFueled` — removes that gap by dovetailing: on `⟨i, fuel⟩` run the
enumerator on `i` for `fuel` steps and emit the decoded output, padding with `source 0`
before it halts.  The emitted stream is poly regardless of how expensive `source` is. -/

/-- The result at fuel `fuel` is stable under larger fuel (bounded interpreter monotonicity). -/
lemma codeEvalnNat_pair_mono {code : Nat.Partrec.Code} {i fuel fuel' v : ℕ}
    (hle : fuel ≤ fuel')
    (hv : codeEvalnNat code (Nat.pair fuel i) = v + 1) :
    codeEvalnNat code (Nat.pair fuel' i) = v + 1 := by
  simp only [codeEvalnNat, Nat.unpair_pair] at hv ⊢
  cases hx : Nat.Partrec.Code.evaln fuel code i with
  | none => rw [hx] at hv; simp at hv
  | some w =>
      rw [hx] at hv
      have h2 : Nat.Partrec.Code.evaln fuel' code i = some w :=
        Nat.Partrec.Code.evaln_mono hle hx
      rw [h2]; omega

/-- A code-enumerable ("c.e.") sentence source: a program that halts on every index `i`
returning `⌜source i⌝`, and whose every output lies in `source`'s range.  This is
*unrestricted* computable enumerability — no clock — rendering `thm:obu`'s "computably
enumerable sequence" premise, not the `def:ec` efficiency class.
Paper node: `thm:obu` -/
structure CEEnumeration (source : ℕ → Sentence) where
  code : Nat.Partrec.Code
  halts : ∀ i, ∃ fuel,
    codeEvalnNat code (Nat.pair fuel i) = Encodable.encode (source i) + 1
  outputs_sound : ∀ z, codeEvalnNat code z ≠ 0 →
    ∃ i, codeEvalnNat code z = Encodable.encode (source i) + 1

/-- Dovetailed stream: `n = ⟨i, fuel⟩ ↦` decoded enumerator output, or `source 0` before it
halts. -/
noncomputable def ceRepeatSeq {source : ℕ → Sentence} (h : CEEnumeration source)
    (n : ℕ) : Sentence :=
  let r := codeEvalnNat h.code (Nat.pair n.unpair.2 n.unpair.1)
  if r = 0 then source 0 else (Encodable.decode (r - 1)).getD (source 0)

lemma ceRepeatSeq_eq_source {source : ℕ → Sentence} (h : CEEnumeration source)
    {n i : ℕ} (hr : codeEvalnNat h.code (Nat.pair n.unpair.2 n.unpair.1)
      = Encodable.encode (source i) + 1) :
    ceRepeatSeq h n = source i := by
  simp only [ceRepeatSeq, hr, Nat.add_sub_cancel, Encodable.encodek, Option.getD_some,
    Nat.add_one_ne_zero, if_false]

lemma ceRepeatSeq_encode {source : ℕ → Sentence} (h : CEEnumeration source) (n : ℕ) :
    Encodable.encode (ceRepeatSeq h n) =
      if codeEvalnNat h.code (Nat.pair n.unpair.2 n.unpair.1) = 0 then
        Encodable.encode (source 0)
      else codeEvalnNat h.code (Nat.pair n.unpair.2 n.unpair.1) - 1 := by
  by_cases hz : codeEvalnNat h.code (Nat.pair n.unpair.2 n.unpair.1) = 0
  · simp [ceRepeatSeq, hz]
  · obtain ⟨i, hi⟩ := h.outputs_sound _ hz
    rw [ceRepeatSeq_eq_source h hi, if_neg hz, hi, Nat.add_sub_cancel]

lemma ceRepeatSeq_codes {source : ℕ → Sentence} (h : CEEnumeration source) :
    PolySentenceCodes (ceRepeatSeq h) := by
  obtain ⟨prog, hprog⟩ := codeEvalnNat_polyFueled h.code
  have rP := hprog.comp (PolyFueled.right.pair PolyFueled.left)
  refine ⟨_, (ifzSel_polyFueled.comp
    (((PolyFueled.const (Encodable.encode (source 0))).pair
      (predc_polyFueled.comp rP)).pair rP)).of_eq (fun n => ?_)⟩
  rw [ceRepeatSeq_encode]
  simp only [Nat.unpair_pair, ifzSelFn, Nat.pred_eq_sub_one]

/-- **General efficient repetition.** Every code-enumerable source has an
efficient-repetition witness — no polynomial-clock assumption on the source itself.
This is the padding-and-repeating transformation `thm:obu`'s paper proof performs
internally (tex:5651-5656), dovetailed under the interpreter clock; the padding element
is `source 0` rather than `⊤`, since `EfficientRepeatedEnumeration.sound` requires
padding from the source's own range.
Paper node: `def:ec`, `thm:obu` -/
noncomputable def EfficientRepeatedEnumeration.ofCE {source : ℕ → Sentence}
    (h : CEEnumeration source) : EfficientRepeatedEnumeration source where
  sequence := ceRepeatSeq h
  sequence_poly := BigSentenceCodes.ofPolySentenceCodes (ceRepeatSeq_codes h)
  repeats := by
    intro i N
    -- `ceRepeatSeq h i` is some `source i'`; that member recurs at arbitrarily large fuel.
    have hsi : ∃ i', ceRepeatSeq h i = source i' := by
      by_cases hz : codeEvalnNat h.code (Nat.pair i.unpair.2 i.unpair.1) = 0
      · exact ⟨0, by simp [ceRepeatSeq, hz]⟩
      · obtain ⟨i', hi'⟩ := h.outputs_sound _ hz
        exact ⟨i', ceRepeatSeq_eq_source h hi'⟩
    obtain ⟨i', hi'⟩ := hsi
    obtain ⟨fuel, hfuel⟩ := h.halts i'
    refine ⟨Nat.pair i' (max fuel N), le_trans (le_max_right _ _) (Nat.right_le_pair _ _), ?_⟩
    rw [hi']
    apply ceRepeatSeq_eq_source h
    simp only [Nat.unpair_pair]
    exact codeEvalnNat_pair_mono (le_max_left _ _) hfuel
  sound j := by
    by_cases hz : codeEvalnNat h.code (Nat.pair j.unpair.2 j.unpair.1) = 0
    · exact ⟨0, by simp [ceRepeatSeq, hz]⟩
    · obtain ⟨i, hi⟩ := h.outputs_sound _ hz
      exact ⟨i, ceRepeatSeq_eq_source h hi⟩
  covers i := by
    obtain ⟨fuel, hfuel⟩ := h.halts i
    refine ⟨Nat.pair i fuel, ceRepeatSeq_eq_source h ?_⟩
    simp only [Nat.unpair_pair]
    exact hfuel

/-- **Uniform Non-Dogmatism at the paper's own premise** (`thm:obu`, tex:1540-1546): the
source enters as a c.e. sequence (`CEEnumeration`), and the padded efficient repetition
the paper builds inside its proof is constructed here by `EfficientRepeatedEnumeration.ofCE`
(dovetailing under the interpreter clock, padding with `source 0` rather than `⊤`).  The
remaining hypothesis `hjoint` is the paper's "Γ ∪ φ‾ is consistent", stagewise.
Paper node: `thm:obu` -/
theorem lic_uniform_nonDogmatism_ofCE
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (source : ℕ → Sentence) (h : CEEnumeration source)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (source i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ limitingBelief P (source i) :=
  lic_uniform_nonDogmatism P DP source (.ofCE h) hjoint

end LogicalInduction
