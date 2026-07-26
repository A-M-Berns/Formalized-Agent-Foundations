import LogicalInduction.Construction.Witnesses.KraftInequality
import LogicalInduction.Properties.OccamBounds
import Mathlib.Data.Nat.Size

/-!
# Concrete prefix machine for Occam Bounds (`M7-PREFIX-MACHINE`, steps 2–5)

This file constructs the concrete self-delimiting sentence code behind the Occam-bound
boundary `PrefixMachinePresentation` (`Properties/OccamBounds.lean`) and discharges every
*mathematical* field of that boundary — the finite Kraft budget (from
`kraft_inequality`), coverage, the exact from-below approximation, and the fixed additive
negation overhead — leaving exactly the fuel-model *emission programs* as the residual
operational input (`PrefixMachineComputation`), in the same style as
`BitPrefixCodeComputation` (`BitPrefixSyntax.lean`).

## The code

A sentence `φ` factors uniquely as `∼^d ρ` with `d = negDepth φ` outer negations
(Foundation's `∼ψ` is literally `ψ 🡒 ⊥`) around a core `ρ = negCore φ`.  Its codeword is
the concatenation of two self-delimiting integer codes

  `sentCode φ = natCode (negDepth φ) ++ natCode (encode (negCore φ))`,

where `natCode n` spends `size (n+1) - 1` unary marker bits, one terminator bit, and
`size (n+1)` payload bits (`2 · size (n+1)` in total).  The prefix complexity is
`prefixKappa φ = |sentCode φ| + 1`; the extra bit halves every weight, which is exactly
the slack the multiplicity-two enumeration below spends.

Factoring the negation depth *out of* the stock `Encodable` code is load-bearing: it is
what makes the negation overhead **additive** (`κ(∼φ) ≤ κ(φ) + 2`, discharged here as
`prefixNegationCompiler` with a real proof), where a plain enumeration code would only
give a multiplicative bound.

## Modeling disclosure (type-`(c)`, recorded at proof time)

`prefixKappa` is the length function of a **fixed, computable** self-delimiting code, not
of a *universal* prefix machine: the paper's `κ` is universal prefix (Kolmogorov)
complexity, which is uncomputable and machine-independent up to a constant.  Every
theorem downstream of `PrefixMachinePresentation` is stated for an arbitrary `κ`, so the
generic paper-faithful statements are unchanged; what this file adds is a genuine,
non-vacuous *instance* whose "simplicity" is code length under this fixed code.  The
universality upgrade (dovetailing over all programs, lower-semicomputable weights) is a
strictly larger construction and remains undone; see `notes/m7-prefix-machine-scope.md`.
-/

namespace LogicalInduction

open LO.Propositional Filter Topology

/-! ## The self-delimiting integer code -/

/-- Self-delimiting binary code of `n`: `size (n+1) - 1` marker bits, a terminator, and
the `size (n+1)` bits of `n+1`.  Total length `2 * size (n+1)`.
Paper node: `thm:ob` -/
def natCode (n : ℕ) : List Bool :=
  List.replicate ((n + 1).size - 1) true ++ false ::
    (List.range (n + 1).size).map (n + 1).testBit

lemma natCode_length (n : ℕ) : (natCode n).length = 2 * (n + 1).size := by
  have hs : 0 < (n + 1).size := Nat.size_pos.mpr (Nat.succ_pos n)
  simp only [natCode, List.length_append, List.length_replicate, List.length_cons,
    List.length_map, List.length_range]
  omega

/-- The unary-marker header forces equal sizes on comparable codewords. -/
lemma replicate_true_false_prefix : ∀ {a b : ℕ} {u v : List Bool},
    (List.replicate a true ++ false :: u) <+: (List.replicate b true ++ false :: v) →
    a = b ∧ u <+: v := by
  intro a
  induction a with
  | zero =>
    intro b u v h
    cases b with
    | zero => simpa using h
    | succ k =>
      rw [List.replicate_zero, List.nil_append, List.replicate_succ,
        List.cons_append, List.cons_prefix_cons] at h
      exact absurd h.1 (by simp)
  | succ k ih =>
    intro b u v h
    cases b with
    | zero =>
      rw [List.replicate_succ, List.cons_append, List.replicate_zero,
        List.nil_append, List.cons_prefix_cons] at h
      exact absurd h.1 (by simp)
    | succ j =>
      rw [List.replicate_succ, List.replicate_succ, List.cons_append,
        List.cons_append, List.cons_prefix_cons] at h
      obtain ⟨he, hp⟩ := ih h.2
      exact ⟨by omega, hp⟩

/-- `natCode` is prefix-free and injective in one statement: a codeword that is a prefix
of another forces equal integers. -/
lemma natCode_prefix_inj {m n : ℕ} (h : natCode m <+: natCode n) : m = n := by
  obtain ⟨hsz, hp⟩ := replicate_true_false_prefix h
  have hm : 0 < (m + 1).size := Nat.size_pos.mpr (Nat.succ_pos m)
  have hn : 0 < (n + 1).size := Nat.size_pos.mpr (Nat.succ_pos n)
  have hs : (m + 1).size = (n + 1).size := by omega
  have hlen : ((List.range (m + 1).size).map (m + 1).testBit).length =
      ((List.range (n + 1).size).map (n + 1).testBit).length := by
    simp [hs]
  have hpayload := hp.eq_of_length hlen
  have hbit : ∀ j, (m + 1).testBit j = (n + 1).testBit j := by
    intro j
    by_cases hj : j < (m + 1).size
    · have := congrArg (fun l => l[j]?) hpayload
      simpa [List.getElem?_map, List.getElem?_range, hj, hs ▸ hj] using this
    · have h1 : (m + 1).testBit j = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (Nat.lt_size_self _)
          (Nat.pow_le_pow_right (by norm_num) (le_of_not_gt hj)))
      have h2 : (n + 1).testBit j = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (Nat.lt_size_self _)
          (Nat.pow_le_pow_right (by norm_num) (le_of_not_gt (hs ▸ hj))))
      rw [h1, h2]
  have := Nat.eq_of_testBit_eq hbit
  omega

/-! ## Negation factoring -/

/-- Number of outermost negations (`∼ψ = ψ 🡒 ⊥` literally). -/
def negDepth : Sentence → ℕ
  | Formula.imp φ Formula.falsum => negDepth φ + 1
  | _ => 0

/-- The sentence stripped of its outermost negations. -/
def negCore : Sentence → Sentence
  | Formula.imp φ Formula.falsum => negCore φ
  | φ => φ

/-- Rebuild `∼^k ρ`. -/
def negIter : ℕ → Sentence → Sentence
  | 0, ρ => ρ
  | k + 1, ρ => Formula.imp (negIter k ρ) Formula.falsum

lemma negDepth_neg (φ : Sentence) : negDepth (∼φ) = negDepth φ + 1 := rfl

lemma negCore_neg (φ : Sentence) : negCore (∼φ) = negCore φ := rfl

/-- Constructor-form restatements (the `∼` notation does not match syntactically after
`cases`). -/
lemma negDepth_imp_falsum (φ : Sentence) :
    negDepth (Formula.imp φ Formula.falsum) = negDepth φ + 1 := rfl

lemma negCore_imp_falsum (φ : Sentence) :
    negCore (Formula.imp φ Formula.falsum) = negCore φ := rfl

/-- The `(negDepth, negCore)` factoring is faithful: it rebuilds the sentence. -/
lemma negIter_negDepth_negCore : ∀ φ : Sentence,
    negIter (negDepth φ) (negCore φ) = φ := by
  intro φ
  induction φ with
  | atom a => rfl
  | falsum => rfl
  | and φ ψ ihφ ihψ => rfl
  | or φ ψ ihφ ihψ => rfl
  | imp φ ψ ihφ ihψ =>
    cases ψ with
    | falsum =>
      show negIter (negDepth φ + 1) (negCore φ) = _
      rw [negIter, ihφ]
    | atom a => rfl
    | and _ _ => rfl
    | or _ _ => rfl
    | imp _ _ => rfl

/-! ## The sentence code and its prefix complexity -/

/-- The self-delimiting sentence codeword: negation depth, then the stock code of the
core, each under `natCode`.
Paper node: `thm:ob` -/
def sentCode (φ : Sentence) : List Bool :=
  natCode (negDepth φ) ++ natCode (Encodable.encode (negCore φ))

lemma sentCode_length (φ : Sentence) :
    (sentCode φ).length =
      2 * (negDepth φ + 1).size + 2 * (Encodable.encode (negCore φ) + 1).size := by
  simp [sentCode, natCode_length]

/-- `sentCode` is prefix-free and injective in one statement. -/
lemma sentCode_prefix_inj {φ ψ : Sentence} (h : sentCode φ <+: sentCode ψ) : φ = ψ := by
  have h1 : natCode (negDepth φ) <+: sentCode ψ :=
    (List.prefix_append _ _).trans h
  have h2 : natCode (negDepth ψ) <+: sentCode ψ := List.prefix_append _ _
  have hd : negDepth φ = negDepth ψ := by
    rcases le_total (natCode (negDepth φ)).length (natCode (negDepth ψ)).length with
      hle | hle
    · exact natCode_prefix_inj (List.prefix_of_prefix_length_le h1 h2 hle)
    · exact (natCode_prefix_inj (List.prefix_of_prefix_length_le h2 h1 hle)).symm
  rw [sentCode, sentCode, hd, List.prefix_append_right_inj] at h
  have hcore : negCore φ = negCore ψ := Encodable.encode_injective (natCode_prefix_inj h)
  calc φ = negIter (negDepth φ) (negCore φ) := (negIter_negDepth_negCore φ).symm
    _ = negIter (negDepth ψ) (negCore ψ) := by rw [hd, hcore]
    _ = ψ := negIter_negDepth_negCore ψ

/-- Prefix complexity of the concrete machine: codeword length plus one slack bit.  The
slack bit halves each weight; the enumeration below spends that factor on its
multiplicity-two index map.
Paper node: `thm:ob` -/
def prefixKappa (φ : Sentence) : ℕ := (sentCode φ).length + 1

/-! ## The concrete enumeration -/

/-- Total sentence enumeration: canonical codes decode to their sentence, every other
index falls back to a fresh atom.  Surjective with index multiplicity at most two.
Paper node: `thm:ob` -/
def prefixSentenceEnum (n : ℕ) : Sentence :=
  match Encodable.decode (α := Sentence) n with
  | some φ => if Encodable.encode φ = n then φ else Formula.atom n
  | none => Formula.atom n

lemma prefixSentenceEnum_encode (φ : Sentence) :
    prefixSentenceEnum (Encodable.encode φ) = φ := by
  simp [prefixSentenceEnum, Encodable.encodek]

lemma prefixSentenceEnum_covers (φ : Sentence) : ∃ i, prefixSentenceEnum i = φ :=
  ⟨Encodable.encode φ, prefixSentenceEnum_encode φ⟩

lemma prefixSentenceEnum_of_not_canonical {n : ℕ}
    (h : ∀ φ : Sentence, Encodable.encode φ ≠ n) :
    prefixSentenceEnum n = Formula.atom n := by
  unfold prefixSentenceEnum
  cases hd : Encodable.decode (α := Sentence) n with
  | none => rfl
  | some φ => simp [h φ]

/-! ## The Kraft budget -/

/-- Half of the Kraft budget covers any injectively indexed sentence family: the
codewords are prefix-free, so `kraft_inequality` bounds the length-weights by one, and
the slack bit halves the total. -/
lemma sum_prefixWeight_le_half {T : Finset ℕ} {f : ℕ → Sentence}
    (hinj : ∀ i ∈ T, ∀ j ∈ T, f i = f j → i = j) :
    ∑ i ∈ T, prefixWeight prefixKappa (f i) ≤ 1 / 2 := by
  classical
  have hterm : ∀ i, prefixWeight prefixKappa (f i) =
      (1 / 2 : ℝ) ^ (sentCode (f i)).length * (1 / 2) := by
    intro i
    rw [prefixWeight, prefixKappa, pow_succ, one_div_pow, mul_one_div, div_div]
  have hcode_inj : ∀ i ∈ T, ∀ j ∈ T, sentCode (f i) = sentCode (f j) → i = j := by
    intro i hi j hj hij
    exact hinj i hi j hj (sentCode_prefix_inj (hij ▸ List.prefix_refl _))
  have hpf : ∀ a ∈ T.image (fun i => sentCode (f i)),
      ∀ b ∈ T.image (fun i => sentCode (f i)), a <+: b → a = b := by
    intro a ha b hb hab
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    rw [sentCode_prefix_inj hab]
  calc ∑ i ∈ T, prefixWeight prefixKappa (f i)
      = (∑ i ∈ T, (1 / 2 : ℝ) ^ (sentCode (f i)).length) * (1 / 2) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (∑ w ∈ T.image (fun i => sentCode (f i)), (1 / 2 : ℝ) ^ w.length) * (1 / 2) := by
        rw [Finset.sum_image hcode_inj]
    _ ≤ 1 * (1 / 2) := by
        have := kraft_inequality hpf
        nlinarith
    _ = 1 / 2 := one_mul _

/-- The finite Kraft budget of the concrete machine over its total enumeration: the
canonical indices and the atom-fallback indices are each injective, and each half of the
budget covers one class.
Paper node: `thm:ob` -/
lemma prefixKraft (N : ℕ) :
    ∑ i ∈ Finset.range N, prefixWeight prefixKappa (prefixSentenceEnum i) ≤ 1 := by
  classical
  have hcanon : ∀ i : ℕ, (∃ φ : Sentence, Encodable.encode φ = i) →
      Encodable.encode (prefixSentenceEnum i) = i := by
    rintro i ⟨φ, rfl⟩
    rw [prefixSentenceEnum_encode]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N)
    (fun i => ∃ φ : Sentence, Encodable.encode φ = i)]
  have h1 : ∑ i ∈ (Finset.range N).filter
        (fun i => ∃ φ : Sentence, Encodable.encode φ = i),
      prefixWeight prefixKappa (prefixSentenceEnum i) ≤ 1 / 2 := by
    apply sum_prefixWeight_le_half
    intro i hi j hj hij
    have hci := hcanon i (Finset.mem_filter.mp hi).2
    have hcj := hcanon j (Finset.mem_filter.mp hj).2
    rw [← hci, ← hcj, hij]
  have h2 : ∑ i ∈ (Finset.range N).filter
        (fun i => ¬ ∃ φ : Sentence, Encodable.encode φ = i),
      prefixWeight prefixKappa (prefixSentenceEnum i) ≤ 1 / 2 := by
    apply sum_prefixWeight_le_half
    intro i hi j hj hij
    have hai : prefixSentenceEnum i = Formula.atom i :=
      prefixSentenceEnum_of_not_canonical
        (fun φ h => (Finset.mem_filter.mp hi).2 ⟨φ, h⟩)
    have haj : prefixSentenceEnum j = Formula.atom j :=
      prefixSentenceEnum_of_not_canonical
        (fun φ h => (Finset.mem_filter.mp hj).2 ⟨φ, h⟩)
    rw [hai, haj] at hij
    exact Formula.atom.inj hij
  linarith

/-! ## The fixed negation compiler (fully discharged) -/

lemma size_succ_le (n : ℕ) : (n + 1 + 1).size ≤ (n + 1).size + 1 := by
  apply Nat.size_le.mpr
  calc n + 1 + 1 ≤ 2 * (n + 1) := by omega
    _ < 2 * 2 ^ (n + 1).size := by
        have := Nat.lt_size_self (n + 1)
        omega
    _ = 2 ^ ((n + 1).size + 1) := by rw [pow_succ]; ring

/-- The concrete negation compiler: prepending one negation extends the depth field of
the codeword by at most two bits, so `κ(∼φ) ≤ κ(φ) + 2`.  This discharges the
`PrefixNegationCompiler` input of `lic_occamBounds` with a real proof (kind `P`;
provenance `(a)` in-project, `(b)` `Nat.size` API).
Paper node: `thm:ob` -/
def prefixNegationCompiler : PrefixNegationCompiler prefixKappa where
  overhead := 2
  complexity_neg_le := fun φ => by
    show (sentCode (∼φ)).length + 1 ≤ (sentCode φ).length + 1 + 2
    rw [sentCode_length, sentCode_length, negDepth_neg, negCore_neg]
    have := size_succ_le (negDepth φ)
    omega

/-! ## The exact from-below approximation -/

/-- Exact rational weight `2^{-κ}` of the `i`-th enumerated sentence — the concrete
machine's `κ` is computable, so the "from-below approximation" is exact and constant in
the stage.
Paper node: `thm:ob` -/
def prefixApprox (i : ℕ) : ℚ :=
  1 / 2 ^ prefixKappa (prefixSentenceEnum i)

lemma prefixApprox_pos (i : ℕ) : 0 < prefixApprox i := by
  rw [prefixApprox]
  positivity

lemma prefixApprox_eq (i : ℕ) :
    ((prefixApprox i : ℚ) : ℝ) = prefixWeight prefixKappa (prefixSentenceEnum i) := by
  rw [prefixApprox, prefixWeight]
  push_cast
  norm_num

/-- Threshold base of the concrete machine, matching `obBase` over the presentation
below: input `z = ⟨j', ⟨n, i⟩⟩` denotes rung `j'+1`, day `n`, sentence index `i`. -/
def prefixEmitBase (z : ℕ) : ℚ :=
  prefixApprox z.unpair.2.unpair.2 /
    (2 * ((z.unpair.1 + 1 : ℕ) : ℚ) ^ 4)

/-! ## Deriving the gate emissions from the weight emission

Both `OccamThresholdEmission` token streams are rational arithmetic on the exact weight:
with `D i = 2^{κ(sentenceᵢ)}` the threshold sum at rung `j'+1` is `1 / (D i · (j'+1)⁴)`
and the inverse width is `2 · D i · (j'+1)⁴`, so both encodings are `mulc`-assembled
pairings of the weight denominator — no separate emission programs are needed. -/

/-- Denominator of the `i`-th exact weight. -/
def prefixDen (i : ℕ) : ℕ := 2 ^ prefixKappa (prefixSentenceEnum i)

lemma prefixDen_pos (i : ℕ) : 0 < prefixDen i := by
  rw [prefixDen]
  positivity

lemma prefixApprox_eq_inv (i : ℕ) : prefixApprox i = ((prefixDen i : ℕ) : ℚ)⁻¹ := by
  rw [prefixApprox, prefixDen, one_div]
  norm_cast

lemma encode_prefixApprox (i : ℕ) :
    Encodable.encode (prefixApprox i) = Nat.pair 2 (prefixDen i) := by
  rw [prefixApprox_eq_inv, encode_rat_inv_natCast (prefixDen_pos i)]

/-- The weight denominator stream extracted from the weight emission. -/
lemma prefixDen_polyFueled (h : PolyRatCodes prefixApprox) :
    ∃ c, PolyFueled c prefixDen := by
  obtain ⟨c, hc⟩ := h
  exact ⟨_, (PolyFueled.right.comp hc).of_eq (fun i => by
    rw [encode_prefixApprox, Nat.unpair_pair])⟩

lemma prefixEmit_sum_eq (z : ℕ) :
    prefixEmitBase z + prefixEmitBase z =
      ((prefixDen z.unpair.2.unpair.2 * (z.unpair.1 + 1) ^ 4 : ℕ) : ℚ)⁻¹ := by
  have hD : (0 : ℚ) < ((prefixDen z.unpair.2.unpair.2 : ℕ) : ℚ) := by
    exact_mod_cast prefixDen_pos z.unpair.2.unpair.2
  have hj : (0 : ℚ) < (((z.unpair.1 + 1 : ℕ) : ℚ)) := by positivity
  rw [prefixEmitBase, prefixApprox_eq_inv]
  push_cast
  field_simp
  ring

lemma prefixEmit_inv_eq (z : ℕ) :
    1 / prefixEmitBase z =
      ((2 * prefixDen z.unpair.2.unpair.2 * (z.unpair.1 + 1) ^ 4 : ℕ) : ℚ) := by
  have hD : (0 : ℚ) < ((prefixDen z.unpair.2.unpair.2 : ℕ) : ℚ) := by
    exact_mod_cast prefixDen_pos z.unpair.2.unpair.2
  have hj : (0 : ℚ) < (((z.unpair.1 + 1 : ℕ) : ℚ)) := by positivity
  rw [prefixEmitBase, prefixApprox_eq_inv]
  push_cast
  field_simp

/-- Common `mulc` assembly: the poly-fueled stream `z ↦ D(i(z)) · (j'(z)+1)⁴`. -/
lemma prefixGateDen_polyFueled (h : PolyRatCodes prefixApprox) :
    ∃ c, PolyFueled c
      (fun z => prefixDen z.unpair.2.unpair.2 * (z.unpair.1 + 1) ^ 4) := by
  obtain ⟨cD, hD⟩ := prefixDen_polyFueled h
  obtain ⟨cm, hm⟩ := mul_polyFueled
  have hj := PolyFueled.left.succ_comp
  have hj2 : PolyFueled ((Nat.Partrec.Code.succ.comp Nat.Partrec.Code.left).pair
        (Nat.Partrec.Code.succ.comp Nat.Partrec.Code.left) |> cm.comp)
      (fun z => (z.unpair.1 + 1) * (z.unpair.1 + 1)) :=
    (hm.comp (hj.pair hj)).of_eq (fun z => by simp only [Nat.unpair_pair])
  have hj4 := (hm.comp (hj2.pair hj2)).of_eq
    (f' := fun z => (z.unpair.1 + 1) ^ 4)
    (fun z => by simp only [Nat.unpair_pair]; ring)
  have hi : PolyFueled (Nat.Partrec.Code.right.comp Nat.Partrec.Code.right)
      (fun z => z.unpair.2.unpair.2) :=
    PolyFueled.right.comp PolyFueled.right
  have hDi := hD.comp hi
  exact ⟨_, (hm.comp (hDi.pair hj4)).of_eq
    (fun z => by simp only [Nat.unpair_pair])⟩

/-- The threshold-sum token stream, derived from the weight emission. -/
lemma prefixThresholdSum_polyRat (h : PolyRatCodes prefixApprox) :
    PolyRatCodes (fun z => prefixEmitBase z + prefixEmitBase z) := by
  obtain ⟨cg, hg⟩ := prefixGateDen_polyFueled h
  refine ⟨_, ((PolyFueled.const 2).pair hg).of_eq (fun z => ?_)⟩
  have hpos : 0 < prefixDen z.unpair.2.unpair.2 * (z.unpair.1 + 1) ^ 4 :=
    Nat.mul_pos (prefixDen_pos _) (by positivity)
  show _ = Encodable.encode (prefixEmitBase z + prefixEmitBase z)
  rw [prefixEmit_sum_eq, encode_rat_inv_natCast hpos]

/-- The inverse-width token stream, derived from the weight emission. -/
lemma prefixInverseWidth_polyRat (h : PolyRatCodes prefixApprox) :
    PolyRatCodes (fun z => 1 / prefixEmitBase z) := by
  obtain ⟨cg, hg⟩ := prefixGateDen_polyFueled h
  obtain ⟨cm, hm⟩ := mul_polyFueled
  have hquad : PolyFueled _ (fun z =>
      4 * (prefixDen z.unpair.2.unpair.2 * (z.unpair.1 + 1) ^ 4)) :=
    (hm.comp ((PolyFueled.const 4).pair hg)).of_eq (fun z => by rw [Nat.unpair_pair])
  refine ⟨_, (hquad.pair (PolyFueled.const 1)).of_eq (fun z => ?_)⟩
  show _ = Encodable.encode (1 / prefixEmitBase z)
  rw [prefixEmit_inv_eq, encode_rat_natCast]
  congr 1
  ring

/-! ## Deriving the weight emission from the sentence emission

`prefixDen i = 2^{κ(sentenceᵢ)}` is arithmetic on the *code* `e = encode (sentenceᵢ)`:
strip the outer negations of `e` by iterating the code-level un-negation step (`dcStep`),
read off `d = negDepth` and `c = encode ∘ negCore` from the final state, and materialize

  `2^κ = 2 · (2^{size (d+1)})² · (2^{size (c+1)})²`

by the halving-driven doubling `p2s` — the doubling loop is clocked by the halving of a
poly-size input, so the iterated state stays `≤ 2(x+1)` and needs no clamp.  Hence
`approx_poly` is *derived* from `sentence_poly` (`approx_polyRat_of_sentence`), and the
residual operational input collapses to the single sentence-code emitter. -/

/-- Code equations of Foundation's `Formula.toNat` on `Sentence` (`α = ℕ`, `encode = id`
on atoms).  All are definitional. -/
lemma encode_falsum' : Encodable.encode (Formula.falsum : Sentence) = 1 := rfl

lemma encode_atom' (a : ℕ) :
    Encodable.encode (Formula.atom a : Sentence) = Nat.pair 1 a + 1 := rfl

lemma encode_imp' (φ ψ : Sentence) :
    Encodable.encode (Formula.imp φ ψ) =
      Nat.pair 2 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1 := rfl

lemma encode_and' (φ ψ : Sentence) :
    Encodable.encode (Formula.and φ ψ) =
      Nat.pair 3 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1 := rfl

lemma encode_or' (φ ψ : Sentence) :
    Encodable.encode (Formula.or φ ψ) =
      Nat.pair 4 (Nat.pair (Encodable.encode φ) (Encodable.encode ψ)) + 1 := rfl

/-- One code-level un-negation step on a state `⟨cur, cnt⟩`: if `cur` is the code of a
negation `ψ 🡒 ⊥` (tag `2`, right child the code `1` of `⊥`), move to
`⟨code of ψ, cnt + 1⟩`; otherwise stay.  Branchless `ifzSelFn` form, chosen to match its
`PolyFueled` assembly literally.
Paper node: `thm:ob` -/
def dcStep (p : ℕ) : ℕ :=
  ifzSelFn
    (Nat.pair (Nat.pair (p.unpair.1 - 1).unpair.2.unpair.1 (p.unpair.2 + 1)) p)
    ((1 - p.unpair.1)
      + (((p.unpair.1 - 1).unpair.1 - 2) + (2 - (p.unpair.1 - 1).unpair.1))
      + (((p.unpair.1 - 1).unpair.2.unpair.2 - 1)
          + (1 - (p.unpair.1 - 1).unpair.2.unpair.2)))

lemma dcStep_of_neg {m : ℕ} (cnt : ℕ) (h1 : 1 ≤ m) (h2 : (m - 1).unpair.1 = 2)
    (h3 : (m - 1).unpair.2.unpair.2 = 1) :
    dcStep (Nat.pair m cnt) = Nat.pair (m - 1).unpair.2.unpair.1 (cnt + 1) := by
  rw [dcStep, ifzSelFn]
  simp only [Nat.unpair_pair]
  rw [if_pos (by omega)]

lemma dcStep_of_stay {m : ℕ} (cnt : ℕ)
    (h : ¬(1 ≤ m ∧ (m - 1).unpair.1 = 2 ∧ (m - 1).unpair.2.unpair.2 = 1)) :
    dcStep (Nat.pair m cnt) = Nat.pair m cnt := by
  rw [dcStep, ifzSelFn]
  simp only [Nat.unpair_pair]
  rw [if_neg (by omega)]

lemma dcStep_encode_neg (φ : Sentence) (cnt : ℕ) :
    dcStep (Nat.pair (Encodable.encode (Formula.imp φ Formula.falsum)) cnt) =
      Nat.pair (Encodable.encode φ) (cnt + 1) := by
  rw [encode_imp', encode_falsum']
  have hm : Nat.pair 2 (Nat.pair (Encodable.encode φ) 1) + 1 - 1 =
      Nat.pair 2 (Nat.pair (Encodable.encode φ) 1) := by omega
  rw [dcStep_of_neg cnt (by omega) (by rw [hm, Nat.unpair_pair])
    (by rw [hm, Nat.unpair_pair, Nat.unpair_pair]), hm, Nat.unpair_pair, Nat.unpair_pair]

lemma dcStep_encode_of_negDepth_zero (φ : Sentence) (h : negDepth φ = 0) (cnt : ℕ) :
    dcStep (Nat.pair (Encodable.encode φ) cnt) = Nat.pair (Encodable.encode φ) cnt := by
  apply dcStep_of_stay
  rintro ⟨h1, h2, h3⟩
  cases φ with
  | atom a =>
      rw [encode_atom', Nat.add_sub_cancel, Nat.unpair_pair] at h2
      omega
  | falsum =>
      rw [encode_falsum'] at h2
      simp at h2
  | and φ ψ =>
      rw [encode_and', Nat.add_sub_cancel, Nat.unpair_pair] at h2
      omega
  | or φ ψ =>
      rw [encode_or', Nat.add_sub_cancel, Nat.unpair_pair] at h2
      omega
  | imp φ ψ =>
      simp only [encode_imp', Nat.add_sub_cancel, Nat.unpair_pair] at h3
      have hψ : ψ = Formula.falsum :=
        Encodable.encode_injective (by rw [h3, encode_falsum'])
      subst hψ
      rw [negDepth_imp_falsum] at h
      omega

/-- Running the un-negation step long enough from the code of `φ` computes the pair
`⟨encode (negCore φ), negDepth φ⟩` (count starting at `cnt`). -/
lemma dcIter_encode : ∀ (φ : Sentence) (j cnt : ℕ), negDepth φ ≤ j →
    dcStep^[j] (Nat.pair (Encodable.encode φ) cnt) =
      Nat.pair (Encodable.encode (negCore φ)) (cnt + negDepth φ) := by
  intro φ
  induction φ with
  | atom a =>
      intro j cnt _
      rw [Function.iterate_fixed (dcStep_encode_of_negDepth_zero _ rfl cnt)]
      rfl
  | falsum =>
      intro j cnt _
      rw [Function.iterate_fixed (dcStep_encode_of_negDepth_zero _ rfl cnt)]
      rfl
  | and φ ψ ihφ ihψ =>
      intro j cnt _
      rw [Function.iterate_fixed (dcStep_encode_of_negDepth_zero _ rfl cnt)]
      rfl
  | or φ ψ ihφ ihψ =>
      intro j cnt _
      rw [Function.iterate_fixed (dcStep_encode_of_negDepth_zero _ rfl cnt)]
      rfl
  | imp φ ψ ihφ ihψ =>
      cases ψ with
      | falsum =>
          intro j cnt hj
          rw [negDepth_imp_falsum] at hj
          obtain ⟨j', rfl⟩ : ∃ j'', j = j'' + 1 := ⟨j - 1, by omega⟩
          rw [Function.iterate_succ_apply, dcStep_encode_neg,
            ihφ j' (cnt + 1) (by omega), negCore_imp_falsum, negDepth_imp_falsum]
          congr 1
          omega
      | atom a =>
          intro j cnt _
          rw [Function.iterate_fixed (dcStep_encode_of_negDepth_zero _ rfl cnt)]
          rfl
      | and _ _ =>
          intro j cnt _
          rw [Function.iterate_fixed (dcStep_encode_of_negDepth_zero _ rfl cnt)]
          rfl
      | or _ _ =>
          intro j cnt _
          rw [Function.iterate_fixed (dcStep_encode_of_negDepth_zero _ rfl cnt)]
          rfl
      | imp _ _ =>
          intro j cnt _
          rw [Function.iterate_fixed (dcStep_encode_of_negDepth_zero _ rfl cnt)]
          rfl

/-- The negation depth is dominated by the sentence code, so running the step `encode φ`
times always saturates. -/
lemma negDepth_le_encode (φ : Sentence) : negDepth φ ≤ Encodable.encode φ := by
  induction φ with
  | atom a => exact Nat.zero_le _
  | falsum => exact Nat.zero_le _
  | and _ _ _ _ => exact Nat.zero_le _
  | or _ _ _ _ => exact Nat.zero_le _
  | imp φ ψ ihφ _ =>
      cases ψ with
      | falsum =>
          rw [negDepth_imp_falsum, encode_imp', encode_falsum']
          have h1 : Encodable.encode φ ≤ Nat.pair (Encodable.encode φ) 1 :=
            Nat.left_le_pair _ _
          have h2 : Nat.pair (Encodable.encode φ) 1 ≤
              Nat.pair 2 (Nat.pair (Encodable.encode φ) 1) := Nat.right_le_pair _ _
          omega
      | atom a => exact Nat.zero_le _
      | and _ _ => exact Nat.zero_le _
      | or _ _ => exact Nat.zero_le _
      | imp _ _ => exact Nat.zero_le _

lemma dcStep_fst_le (p : ℕ) : (dcStep p).unpair.1 ≤ p.unpair.1 := by
  rw [dcStep, ifzSelFn]
  split
  · rename_i ht
    rw [Nat.unpair_pair]
    simp only [Nat.unpair_pair]
    have h1 := Nat.unpair_left_le (p.unpair.1 - 1).unpair.2
    have h2 := Nat.unpair_right_le (p.unpair.1 - 1)
    omega
  · rw [Nat.unpair_pair]

lemma dcStep_snd_le (p : ℕ) : (dcStep p).unpair.2 ≤ p.unpair.2 + 1 := by
  rw [dcStep, ifzSelFn]
  split
  · simp only [Nat.unpair_pair]
    omega
  · simp only [Nat.unpair_pair]
    omega

lemma dcIter_le (p : ℕ) : ∀ j,
    (dcStep^[j] p).unpair.1 ≤ p.unpair.1 ∧ (dcStep^[j] p).unpair.2 ≤ p.unpair.2 + j := by
  intro j
  induction j with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨le_trans (dcStep_fst_le _) ih.1,
        le_trans (dcStep_snd_le _) (by omega)⟩

/-- The saturating un-negation scan `⟨e, j⟩ ↦ dcStep^[j] ⟨e, 0⟩` is poly-fueled: a `prec`
whose state components never exceed `⟨e, j⟩`. -/
lemma dcIter_polyFueled :
    ∃ c, PolyFueled c (fun m => dcStep^[m.unpair.2] (Nat.pair m.unpair.1 0)) := by
  obtain ⟨cad, had⟩ := addc_polyFueled
  have prevPF := PolyFueled.right.comp PolyFueled.right
  have curPF := PolyFueled.left.comp prevPF
  have cntPF := PolyFueled.right.comp prevPF
  have m1PF := predc_polyFueled.comp curPF
  have idxPF := PolyFueled.left.comp m1PF
  have ccPF := PolyFueled.right.comp m1PF
  have b2PF := PolyFueled.right.comp ccPF
  have stripPF := PolyFueled.left.comp ccPF
  have t1PF := subc_polyFueled.comp ((PolyFueled.const 1).pair curPF)
  have ne2PF := had.comp ((subc_polyFueled.comp (idxPF.pair (PolyFueled.const 2))).pair
    (subc_polyFueled.comp ((PolyFueled.const 2).pair idxPF)))
  have ne1PF := had.comp ((subc_polyFueled.comp (b2PF.pair (PolyFueled.const 1))).pair
    (subc_polyFueled.comp ((PolyFueled.const 1).pair b2PF)))
  have tPF := had.comp ((had.comp (t1PF.pair ne2PF)).pair ne1PF)
  have brPF := (stripPF.pair cntPF.succ_comp).pair prevPF
  have gPF : PolyFueled _ (fun z => dcStep (z.unpair.2.unpair.2)) :=
    (ifzSel_polyFueled.comp (brPF.pair tPF)).of_eq (fun z => by
      simp only [Nat.unpair_pair, dcStep, Nat.pred_eq_sub_one])
  have hst : IsPolyBounded (fun m => dcStep^[m.unpair.2] (Nat.pair m.unpair.1 0)) := by
    apply (isPolyBounded_fst.pair isPolyBounded_snd).of_le
    intro m
    obtain ⟨h1, h2⟩ := dcIter_le (Nat.pair m.unpair.1 0) m.unpair.2
    rw [Nat.unpair_pair] at h1 h2
    calc dcStep^[m.unpair.2] (Nat.pair m.unpair.1 0)
        = Nat.pair (dcStep^[m.unpair.2] (Nat.pair m.unpair.1 0)).unpair.1
            (dcStep^[m.unpair.2] (Nat.pair m.unpair.1 0)).unpair.2 :=
          (Nat.pair_unpair _).symm
      _ ≤ Nat.pair m.unpair.1 m.unpair.2 :=
          le_trans (pair_le_pair_left' _ h1) (pair_le_pair_right' _ (by omega))
  exact ⟨_, PolyFueled.prec (PolyFueled.id.pair (PolyFueled.const 0)) gPF
    (st := fun a j => dcStep^[j] (Nat.pair a 0))
    (fun a => by simp)
    (fun a j => by simp only [Nat.unpair_pair, Function.iterate_succ_apply'])
    hst⟩

/-- The `⟨encode ∘ negCore, negDepth⟩` stream of any poly-emitted sentence family. -/
lemma negFields_polyFueled (h : PolySentenceCodes prefixSentenceEnum) :
    ∃ c, PolyFueled c (fun n =>
      Nat.pair (Encodable.encode (negCore (prefixSentenceEnum n)))
        (negDepth (prefixSentenceEnum n))) := by
  obtain ⟨cs, hs⟩ := h
  obtain ⟨cd, hd⟩ := dcIter_polyFueled
  refine ⟨_, (hd.comp (hs.pair hs)).of_eq (fun n => ?_)⟩
  simp only [Nat.unpair_pair]
  rw [dcIter_encode (prefixSentenceEnum n) _ 0 (negDepth_le_encode _), Nat.zero_add]

/-! ### Materializing `2^{size (x+1)}` by halving-driven doubling -/

/-- `p2s x = 2^{size (x+1)}` — the power-of-two envelope of `x + 1`, and the factor a
`natCode` field contributes to the weight denominator (`≤ 2 (x+1)`, so poly-size). -/
def p2s (x : ℕ) : ℕ := 2 ^ (x + 1).size

lemma two_pow_size_le {y : ℕ} (hy : 0 < y) : 2 ^ y.size ≤ 2 * y := by
  have h1 : 0 < y.size := Nat.size_pos.mpr hy
  have h2 : 2 ^ (y.size - 1) ≤ y := by
    by_contra hcon
    have : y.size ≤ y.size - 1 := Nat.size_le.mpr (by omega)
    omega
  have hs : y.size - 1 + 1 = y.size := by omega
  have hp : 2 ^ y.size = 2 ^ (y.size - 1) * 2 := by rw [← hs, pow_succ, hs]
  omega

lemma p2s_le (x : ℕ) : p2s x ≤ 2 * (x + 1) := two_pow_size_le (Nat.succ_pos x)

/-- One step of the halving-driven doubling on a state `⟨cur, pow⟩`: while `cur > 0`,
halve `cur` and double `pow`; once `cur = 0`, stay.  The doubling is clocked by the
halving, so `pow ≤ 2 (x+1)` throughout — no clamp needed. -/
def p2sStep (p : ℕ) : ℕ :=
  ifzSelFn (Nat.pair p (Nat.pair (p.unpair.1 / 2) (p.unpair.2 + p.unpair.2))) p.unpair.1

lemma p2sStep_spec (x j : ℕ) :
    p2sStep (Nat.pair ((x + 1) / 2 ^ j) (2 ^ min j (x + 1).size)) =
      Nat.pair ((x + 1) / 2 ^ (j + 1)) (2 ^ min (j + 1) (x + 1).size) := by
  have hp : (0 : ℕ) < 2 ^ j := Nat.pow_pos (by norm_num)
  by_cases hc : (x + 1) / 2 ^ j = 0
  · have hlt : x + 1 < 2 ^ j := by
      rw [Nat.div_eq_zero_iff] at hc
      omega
    have hs : (x + 1).size ≤ j := Nat.size_le.mpr hlt
    have h1 : (x + 1) / 2 ^ (j + 1) = 0 :=
      Nat.div_eq_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [p2sStep, ifzSelFn]
    simp only [Nat.unpair_pair, hc, if_true]
    rw [h1, Nat.min_eq_right hs, Nat.min_eq_right (by omega)]
  · have h2j : 2 ^ j ≤ x + 1 := by
      rw [Nat.div_eq_zero_iff] at hc
      omega
    have hjs : j < (x + 1).size := by
      by_contra hcon
      have := Nat.size_le.mp (le_of_not_gt hcon)
      omega
    rw [p2sStep, ifzSelFn]
    simp only [Nat.unpair_pair]
    rw [if_neg hc, Nat.div_div_eq_div_mul, ← pow_succ,
      Nat.min_eq_left (by omega), Nat.min_eq_left (by omega), ← Nat.mul_two, ← pow_succ]

/-- `p2s` is poly-fueled. -/
lemma p2s_polyFueled : ∃ c, PolyFueled c p2s := by
  obtain ⟨cdm, hdm⟩ := divmodc_polyFueled 2 (by norm_num)
  obtain ⟨cad, had⟩ := addc_polyFueled
  have prevPF := PolyFueled.right.comp PolyFueled.right
  have curPF := PolyFueled.left.comp prevPF
  have powPF := PolyFueled.right.comp prevPF
  have halfPF : PolyFueled _ (fun z => z.unpair.2.unpair.2.unpair.1 / 2) :=
    (PolyFueled.left.comp (hdm.comp curPF)).of_eq (fun z => by
      simp only [Nat.unpair_pair])
  have dblPF : PolyFueled _ (fun z =>
      z.unpair.2.unpair.2.unpair.2 + z.unpair.2.unpair.2.unpair.2) :=
    (had.comp (powPF.pair powPF)).of_eq (fun z => by simp only [Nat.unpair_pair])
  have gPF : PolyFueled _ (fun z => p2sStep (z.unpair.2.unpair.2)) :=
    (ifzSel_polyFueled.comp ((prevPF.pair (halfPF.pair dblPF)).pair curPF)).of_eq
      (fun z => by simp only [Nat.unpair_pair, p2sStep])
  have hst : IsPolyBounded (fun m =>
      Nat.pair ((m.unpair.1 + 1) / 2 ^ m.unpair.2)
        (2 ^ min m.unpair.2 (m.unpair.1 + 1).size)) := by
    apply ((isPolyBounded_fst.add_one).pair
      ((isPolyBounded_mul_const 2).comp isPolyBounded_fst.add_one)).of_le
    intro m
    have h1 : (m.unpair.1 + 1) / 2 ^ m.unpair.2 ≤ m.unpair.1 + 1 := Nat.div_le_self _ _
    have h2 : 2 ^ min m.unpair.2 (m.unpair.1 + 1).size ≤ 2 * (m.unpair.1 + 1) :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.min_le_right _ _))
        (two_pow_size_le (Nat.succ_pos _))
    exact le_trans (pair_le_pair_left' _ h1)
      (pair_le_pair_right' _ (by omega))
  have hprec := PolyFueled.prec ((PolyFueled.id.succ_comp).pair (PolyFueled.const 1)) gPF
    (st := fun a j => Nat.pair ((a + 1) / 2 ^ j) (2 ^ min j (a + 1).size))
    (fun a => by simp)
    (fun a j => by
      simp only [Nat.unpair_pair]
      exact (p2sStep_spec a j).symm)
    hst
  refine ⟨_, (PolyFueled.right.comp
    (hprec.comp (PolyFueled.id.pair PolyFueled.id.succ_comp))).of_eq (fun x => ?_)⟩
  simp only [Nat.unpair_pair]
  rw [Nat.min_eq_right (Nat.size_le.mpr (Nat.lt_pow_self (by norm_num)))]
  rfl

/-! ### The weight denominator as arithmetic on the negation fields -/

lemma prefixKappa_eq (φ : Sentence) :
    prefixKappa φ =
      2 * (negDepth φ + 1).size + 2 * (Encodable.encode (negCore φ) + 1).size + 1 := by
  rw [prefixKappa, sentCode_length]

lemma prefixDen_eq (i : ℕ) :
    prefixDen i = 2 * p2s (negDepth (prefixSentenceEnum i)) ^ 2 *
      p2s (Encodable.encode (negCore (prefixSentenceEnum i))) ^ 2 := by
  rw [prefixDen, prefixKappa_eq, p2s, p2s]
  generalize (negDepth (prefixSentenceEnum i) + 1).size = a
  generalize (Encodable.encode (negCore (prefixSentenceEnum i)) + 1).size = b
  rw [pow_add, pow_add, pow_one, ← pow_mul, ← pow_mul]
  ring

/-- **The weight emission is derived from the sentence emission.**  Given a poly-fueled
emitter of `encode (prefixSentenceEnum n)`, the exact weights `prefixApprox` are emitted
by stripping negations (`dcIter`), materializing the two `natCode` power-of-two factors
(`p2s`), and pairing the rational encode `⟨2, 2^κ⟩` (kind `C`; provenance `(a)`
throughout — `dcIter_encode`, `p2s_polyFueled`, `encode_prefixApprox`).
Paper node: `thm:ob` -/
theorem approx_polyRat_of_sentence (h : PolySentenceCodes prefixSentenceEnum) :
    PolyRatCodes prefixApprox := by
  obtain ⟨cnf, hnf⟩ := negFields_polyFueled h
  obtain ⟨cp, hp⟩ := p2s_polyFueled
  obtain ⟨cm, hm⟩ := mul_polyFueled
  have hc := (PolyFueled.left.comp hnf).of_eq
    (f' := fun n => Encodable.encode (negCore (prefixSentenceEnum n)))
    (fun n => by simp only [Nat.unpair_pair])
  have hd := (PolyFueled.right.comp hnf).of_eq
    (f' := fun n => negDepth (prefixSentenceEnum n))
    (fun n => by simp only [Nat.unpair_pair])
  have hpd := hp.comp hd
  have hpc := hp.comp hc
  have hpd2 := (hm.comp (hpd.pair hpd)).of_eq
    (f' := fun n => p2s (negDepth (prefixSentenceEnum n)) *
      p2s (negDepth (prefixSentenceEnum n)))
    (fun n => by simp only [Nat.unpair_pair])
  have hpc2 := (hm.comp (hpc.pair hpc)).of_eq
    (f' := fun n => p2s (Encodable.encode (negCore (prefixSentenceEnum n))) *
      p2s (Encodable.encode (negCore (prefixSentenceEnum n))))
    (fun n => by simp only [Nat.unpair_pair])
  have hprod := (hm.comp ((hm.comp ((PolyFueled.const 2).pair hpd2)).pair hpc2)).of_eq
    (f' := fun n => prefixDen n)
    (fun n => by
      simp only [Nat.unpair_pair]
      rw [prefixDen_eq, pow_two, pow_two])
  exact ⟨_, ((PolyFueled.const 2).pair hprod).of_eq (fun n => by
    rw [encode_prefixApprox])⟩

/-! ## Canonicity of sentence codes

`prefixSentenceEnum n` is `decode n` when `n` is canonical (`n ∈ range encode`) and the
fallback `atom n` otherwise, so its emitted code is `n` or `pair 1 n + 1` according to a
single canonicity **bit**.  `validCode` decides that bit by structural descent over
`Formula.toNat`'s tagged-pair format; `sentencePoly_of_invalidBit` reduces the whole
residual `sentence_poly` certificate to a poly-fueled emitter of the bit. -/

/-- Canonicity of a sentence code: is `n` in the range of `Formula.toNat`?  Tag `0` is
`⊥` (payload must be `0`), tag `1` is an atom (any payload), tags `2`–`4` recurse into
both `unpair` children, anything else is garbage.
Paper node: `thm:ob` -/
def validCode : ℕ → Bool
  | 0 => false
  | (e + 1) =>
    if e.unpair.1 = 0 then decide (e.unpair.2 = 0)
    else if e.unpair.1 = 1 then true
    else if e.unpair.1 ≤ 4 then
      have h1 : e.unpair.2.unpair.1 < e + 1 :=
        Nat.lt_succ_iff.mpr (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _))
      have h2 : e.unpair.2.unpair.2 < e + 1 :=
        Nat.lt_succ_iff.mpr (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _))
      validCode e.unpair.2.unpair.1 && validCode e.unpair.2.unpair.2
    else false

/-- Unfolding of `validCode` on a tagged pair. -/
lemma validCode_pair_tag (k c : ℕ) :
    validCode (Nat.pair k c + 1) =
      if k = 0 then decide (c = 0)
      else if k = 1 then true
      else if k ≤ 4 then validCode c.unpair.1 && validCode c.unpair.2
      else false := by
  rw [validCode]
  simp only [Nat.unpair_pair]

/-- Every canonical code is accepted. -/
lemma validCode_encode : ∀ φ : Sentence, validCode (Encodable.encode φ) = true := by
  intro φ
  induction φ with
  | atom a =>
      rw [encode_atom', validCode_pair_tag]
      norm_num
  | falsum =>
      rw [show Encodable.encode (Formula.falsum : Sentence) = Nat.pair 0 0 + 1 from rfl,
        validCode_pair_tag]
      norm_num
  | and φ ψ ihφ ihψ =>
      rw [encode_and', validCode_pair_tag]
      norm_num [Nat.unpair_pair, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      rw [encode_or', validCode_pair_tag]
      norm_num [Nat.unpair_pair, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      rw [encode_imp', validCode_pair_tag]
      norm_num [Nat.unpair_pair, ihφ, ihψ]

/-- Every accepted code is canonical. -/
lemma of_validCode : ∀ n, validCode n = true → ∃ φ : Sentence, Encodable.encode φ = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => intro h; rw [validCode] at h; exact absurd h (by simp)
    | (e + 1) =>
      intro h
      rw [validCode] at h
      by_cases h0 : e.unpair.1 = 0
      · rw [if_pos h0] at h
        have hc : e.unpair.2 = 0 := by simpa using h
        have he : e = 0 := by
          have := Nat.pair_unpair e
          rw [h0, hc] at this
          simpa using this.symm
        exact ⟨Formula.falsum, by rw [he]; rfl⟩
      · rw [if_neg h0] at h
        by_cases h1 : e.unpair.1 = 1
        · refine ⟨Formula.atom e.unpair.2, ?_⟩
          rw [encode_atom', ← h1, Nat.pair_unpair]
        · rw [if_neg h1] at h
          by_cases h4 : e.unpair.1 ≤ 4
          · rw [if_pos h4] at h
            obtain ⟨hv1, hv2⟩ : validCode e.unpair.2.unpair.1 = true ∧
                validCode e.unpair.2.unpair.2 = true := by simpa using h
            have hlt1 : e.unpair.2.unpair.1 < e + 1 :=
              Nat.lt_succ_iff.mpr (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _))
            have hlt2 : e.unpair.2.unpair.2 < e + 1 :=
              Nat.lt_succ_iff.mpr (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _))
            obtain ⟨φ₁, hφ₁⟩ := ih _ hlt1 hv1
            obtain ⟨φ₂, hφ₂⟩ := ih _ hlt2 hv2
            have hpc : Nat.pair e.unpair.2.unpair.1 e.unpair.2.unpair.2 = e.unpair.2 :=
              Nat.pair_unpair _
            have htag : e.unpair.1 = 2 ∨ e.unpair.1 = 3 ∨ e.unpair.1 = 4 := by omega
            rcases htag with h2 | h3 | h4'
            · exact ⟨Formula.imp φ₁ φ₂,
                by rw [encode_imp', hφ₁, hφ₂, hpc, ← h2, Nat.pair_unpair]⟩
            · exact ⟨Formula.and φ₁ φ₂,
                by rw [encode_and', hφ₁, hφ₂, hpc, ← h3, Nat.pair_unpair]⟩
            · exact ⟨Formula.or φ₁ φ₂,
                by rw [encode_or', hφ₁, hφ₂, hpc, ← h4', Nat.pair_unpair]⟩
          · rw [if_neg h4] at h
            exact absurd h (by simp)

/-- The emitted code of the total enumeration, as a function of the canonicity bit. -/
lemma encode_prefixSentenceEnum (n : ℕ) :
    Encodable.encode (prefixSentenceEnum n) =
      if validCode n then n else Nat.pair 1 n + 1 := by
  by_cases hv : validCode n
  · obtain ⟨φ, rfl⟩ := of_validCode n hv
    rw [prefixSentenceEnum_encode, if_pos hv]
  · rw [prefixSentenceEnum_of_not_canonical
      (fun φ he => hv (by rw [← he]; exact validCode_encode φ)),
      encode_atom', if_neg hv]

/-- The canonicity bit, arithmetized: `0` on canonical codes, `1` on fallback indices. -/
def invalidBit (n : ℕ) : ℕ := if validCode n then 0 else 1

/-- **The residual sentence emission reduces to the canonicity bit**: a poly-fueled
emitter of `invalidBit` yields the full `sentence_poly` certificate, since the emitted
value is `n` itself or the atom fallback `pair 1 n + 1` — both trivially assembled
(kind `C`; provenance `(a)`: `encode_prefixSentenceEnum`, `of_validCode`,
`validCode_encode`).
Paper node: `thm:ob` -/
theorem sentencePoly_of_invalidBit (h : ∃ c, PolyFueled c invalidBit) :
    PolySentenceCodes prefixSentenceEnum := by
  obtain ⟨cv, hv⟩ := h
  refine ⟨_, (ifzSel_polyFueled.comp
    ((PolyFueled.id.pair
      (((PolyFueled.const 1).pair PolyFueled.id).succ_comp)).pair hv)).of_eq
    (fun n => ?_)⟩
  simp only [Nat.unpair_pair, ifzSelFn, encode_prefixSentenceEnum]
  by_cases hb : validCode n <;> simp [invalidBit, hb]

/-! ## The canonicity bit by breadth-first descent

`validCode` is tree-recursive over both `unpair` children — inexpressible directly as a
single `prec` chain (a course-of-values table has exponential *value* in this fuel
model).  But the recursion tree is shallow and narrow: children shrink as `√`, so after
`D(n) = size (size n) + 3` levels every slot is resolved to `0`/`1`, and level `d` has
`2^d ≤ O(size n)` slots each `≤ sbChain n d` (the iterated-`√` bound).  This section
builds the *specification* layer: the slot-step `chL`/`chR` (with `0` = invalid and
`1 = encode ⊥` = valid as absorbing resolved slots), the level iteration, conservation
of the conjunction, the shrink bound, and resolution.  The next section will drive the
packed (fixed-width, level-varying base) form through `PolyFueled.prec`. -/

lemma unpair_fst_le_sqrt (n : ℕ) : n.unpair.1 ≤ Nat.sqrt n := by
  simp only [Nat.unpair]
  split_ifs with h
  · exact le_of_lt h
  · exact le_rfl

lemma unpair_snd_le_sqrt (n : ℕ) : n.unpair.2 ≤ Nat.sqrt n := by
  simp only [Nat.unpair]
  split_ifs with h
  · exact le_rfl
  · have := Nat.sqrt_le_add n
    omega

/-- Left child of a slot: resolved slots (`0` invalid, `1` = `⊥` valid, atoms, garbage)
emit their own resolution; tags `2`–`4` emit the left `unpair` child of the payload. -/
def chL (m : ℕ) : ℕ :=
  if m = 0 then 0
  else if (m - 1).unpair.1 = 0 then (if (m - 1).unpair.2 = 0 then 1 else 0)
  else if (m - 1).unpair.1 = 1 then 1
  else if (m - 1).unpair.1 ≤ 4 then (m - 1).unpair.2.unpair.1
  else 0

/-- Right child of a slot. -/
def chR (m : ℕ) : ℕ :=
  if m = 0 then 0
  else if (m - 1).unpair.1 = 0 then (if (m - 1).unpair.2 = 0 then 1 else 0)
  else if (m - 1).unpair.1 = 1 then 1
  else if (m - 1).unpair.1 ≤ 4 then (m - 1).unpair.2.unpair.2
  else 0

lemma validCode_zero : validCode 0 = false := by rw [validCode]

lemma validCode_one : validCode 1 = true := by
  have h := validCode_pair_tag 0 0
  norm_num [Nat.pair] at h
  exact h

/-- One-step conservation: a slot's validity is the conjunction of its children's. -/
lemma validCode_ch (m : ℕ) : validCode m = (validCode (chL m) && validCode (chR m)) := by
  match m with
  | 0 => simp [chL, chR, validCode_zero]
  | (e + 1) =>
    rw [validCode]
    simp only [chL, chR, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    by_cases h0 : e.unpair.1 = 0
    · by_cases hc : e.unpair.2 = 0
      · simp [h0, hc, validCode_one]
      · simp [h0, hc, validCode_zero]
    · by_cases h1 : e.unpair.1 = 1
      · simp [h0, h1, validCode_one]
      · by_cases h4 : e.unpair.1 ≤ 4
        · simp [h0, h1, h4]
        · simp [h0, h1, h4, validCode_zero]

lemma chL_le (m : ℕ) : chL m ≤ Nat.sqrt m + 1 := by
  rw [chL]
  split_ifs with h0 h1 h2 h3 h4
  · omega
  · omega
  · omega
  · omega
  · calc (m - 1).unpair.2.unpair.1 ≤ Nat.sqrt ((m - 1).unpair.2) := unpair_fst_le_sqrt _
      _ ≤ Nat.sqrt m := Nat.sqrt_le_sqrt (le_trans (Nat.unpair_right_le _) (by omega))
      _ ≤ Nat.sqrt m + 1 := by omega
  · omega

lemma chR_le (m : ℕ) : chR m ≤ Nat.sqrt m + 1 := by
  rw [chR]
  split_ifs with h0 h1 h2 h3 h4
  · omega
  · omega
  · omega
  · omega
  · calc (m - 1).unpair.2.unpair.2 ≤ Nat.sqrt ((m - 1).unpair.2) := unpair_snd_le_sqrt _
      _ ≤ Nat.sqrt m := Nat.sqrt_le_sqrt (le_trans (Nat.unpair_right_le _) (by omega))
      _ ≤ Nat.sqrt m + 1 := by omega
  · omega

lemma chL_le_one (m : ℕ) (h : m ≤ 2) : chL m ≤ 1 := by
  interval_cases m <;> decide

lemma chR_le_one (m : ℕ) (h : m ≤ 2) : chR m ≤ 1 := by
  interval_cases m <;> decide

/-- One level of the breadth-first descent (list specification). -/
def levelStep : List ℕ → List ℕ
  | [] => []
  | m :: L => chL m :: chR m :: levelStep L

/-- The levels, with the per-level reversal the packed accumulator produces. -/
def levelsM (n : ℕ) : ℕ → List ℕ
  | 0 => [n]
  | d + 1 => levelStep (levelsM n d).reverse

lemma levelStep_all (L : List ℕ) :
    (levelStep L).all validCode = L.all validCode := by
  induction L with
  | nil => rfl
  | cons m L ih =>
      rw [levelStep, List.all_cons, List.all_cons, List.all_cons, ih,
        ← Bool.and_assoc, ← validCode_ch]

/-- **Conservation**: the conjunction over any level is the root's validity bit. -/
lemma levelsM_all (n : ℕ) : ∀ d, (levelsM n d).all validCode = validCode n := by
  intro d
  induction d with
  | zero => simp [levelsM]
  | succ d ih => rw [levelsM, levelStep_all, List.all_reverse, ih]

lemma mem_levelStep {m' : ℕ} : ∀ {L : List ℕ}, m' ∈ levelStep L →
    ∃ m ∈ L, m' = chL m ∨ m' = chR m := by
  intro L
  induction L with
  | nil => intro h; exact absurd h (by simp [levelStep])
  | cons m L ih =>
      intro h
      rw [levelStep, List.mem_cons, List.mem_cons] at h
      rcases h with rfl | rfl | h
      · exact ⟨m, by simp, Or.inl rfl⟩
      · exact ⟨m, by simp, Or.inr rfl⟩
      · obtain ⟨p, hp, hc⟩ := ih h
        exact ⟨p, by simp [hp], hc⟩

/-- The iterated-`√` slot bound. -/
def sbChain (n : ℕ) : ℕ → ℕ
  | 0 => n
  | d + 1 => Nat.sqrt (sbChain n d) + 1

lemma levelsM_le (n : ℕ) : ∀ d, ∀ m ∈ levelsM n d, m ≤ sbChain n d := by
  intro d
  induction d with
  | zero => intro m hm; rw [levelsM, List.mem_singleton] at hm; simp [hm, sbChain]
  | succ d ih =>
      intro m' hm'
      rw [levelsM] at hm'
      obtain ⟨m, hm, hc⟩ := mem_levelStep hm'
      rw [List.mem_reverse] at hm
      have hle : m ≤ sbChain n d := ih m hm
      have hs : Nat.sqrt m + 1 ≤ sbChain n (d + 1) := by
        rw [sbChain]
        exact Nat.add_le_add_right (Nat.sqrt_le_sqrt hle) 1
      rcases hc with rfl | rfl
      · exact le_trans (chL_le m) hs
      · exact le_trans (chR_le m) hs

lemma size_sqrt_succ_le (x : ℕ) :
    (Nat.sqrt x + 1).size ≤ (x.size + 1) / 2 + 1 := by
  have hx : x < 2 ^ x.size := Nat.lt_size_self x
  have hle : x.size ≤ (x.size + 1) / 2 * 2 := by omega
  have h2 : x < 2 ^ ((x.size + 1) / 2) * 2 ^ ((x.size + 1) / 2) := by
    calc x < 2 ^ x.size := hx
      _ ≤ 2 ^ ((x.size + 1) / 2 * 2) := Nat.pow_le_pow_right (by norm_num) hle
      _ = 2 ^ ((x.size + 1) / 2) * 2 ^ ((x.size + 1) / 2) := by
          rw [← pow_add]
          congr 1
          omega
  have hs : Nat.sqrt x < 2 ^ ((x.size + 1) / 2) := Nat.sqrt_lt.mpr h2
  apply Nat.size_le.mpr
  have hpos : (0:ℕ) < 2 ^ ((x.size + 1) / 2) := Nat.pow_pos (by norm_num)
  calc Nat.sqrt x + 1 < 2 ^ ((x.size + 1) / 2) + 2 ^ ((x.size + 1) / 2) := by omega
    _ = 2 ^ ((x.size + 1) / 2 + 1) := by rw [pow_succ, Nat.mul_two]

lemma sbChain_size_le (n : ℕ) : ∀ d, (sbChain n d).size ≤ n.size / 2 ^ d + 3 := by
  intro d
  induction d with
  | zero => simp [sbChain]
  | succ d ih =>
      rw [sbChain]
      calc (Nat.sqrt (sbChain n d) + 1).size
          ≤ ((sbChain n d).size + 1) / 2 + 1 := size_sqrt_succ_le _
        _ ≤ (n.size / 2 ^ d + 3 + 1) / 2 + 1 := by omega
        _ = n.size / 2 ^ d / 2 + 3 := by omega
        _ = n.size / 2 ^ (d + 1) + 3 := by
            rw [Nat.div_div_eq_div_mul, ← pow_succ]

/-- After `size (size n) + 2` levels the slot bound has collapsed to `2`. -/
lemma sbChain_le_two (n : ℕ) : sbChain n (n.size.size + 2) ≤ 2 := by
  have h7 : sbChain n n.size.size ≤ 7 := by
    have h := sbChain_size_le n n.size.size
    have hz : n.size / 2 ^ n.size.size = 0 :=
      Nat.div_eq_of_lt (Nat.lt_size_self _)
    rw [hz] at h
    have := Nat.size_le.mp (le_trans h (by norm_num) : (sbChain n n.size.size).size ≤ 3)
    omega
  have h3 : sbChain n (n.size.size + 1) ≤ 3 := by
    rw [sbChain]
    have : Nat.sqrt (sbChain n n.size.size) < 3 := Nat.sqrt_lt.mpr (by omega)
    omega
  rw [show n.size.size + 2 = n.size.size + 1 + 1 from rfl, sbChain]
  have : Nat.sqrt (sbChain n (n.size.size + 1)) < 2 := Nat.sqrt_lt.mpr (by omega)
  omega

/-- **Resolution**: at depth `size (size n) + 3` every slot is a resolved bit. -/
lemma levelsM_resolved (n : ℕ) :
    ∀ m ∈ levelsM n (n.size.size + 3), m ≤ 1 := by
  intro m' hm'
  rw [show n.size.size + 3 = n.size.size + 2 + 1 from rfl, levelsM] at hm'
  obtain ⟨m, hm, hc⟩ := mem_levelStep hm'
  rw [List.mem_reverse] at hm
  have hle : m ≤ 2 := le_trans (levelsM_le n _ m hm) (sbChain_le_two n)
  rcases hc with rfl | rfl
  · exact chL_le_one m hle
  · exact chR_le_one m hle

lemma length_levelStep (L : List ℕ) : (levelStep L).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons m L ih => rw [levelStep]; simp [ih]; omega

lemma length_levelsM (n : ℕ) : ∀ d, (levelsM n d).length = 2 ^ d := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih => rw [levelsM, length_levelStep, List.length_reverse, ih, pow_succ]; ring

/-- On a resolved level the validity conjunction is the all-ones test. -/
lemma all_validCode_eq_all_one (L : List ℕ) (h : ∀ m ∈ L, m ≤ 1) :
    L.all validCode = L.all (· == 1) := by
  induction L with
  | nil => rfl
  | cons m L ih =>
      rw [List.all_cons, List.all_cons, ih (fun m hm => h m (by simp [hm]))]
      congr 1
      have hm : m ≤ 1 := h m (by simp)
      interval_cases m
      · simp [validCode_zero]
      · simp [validCode_one]

/-! ## Residual operational input and the assembled boundary -/

/-- Compact operational input for the concrete prefix machine: the single fuel-model
program emitting the enumerated sentence codes.  This is the only field of the Occam
boundary not discharged by this file; it is a conclusion-free emission certificate in
the style of `BitPrefixCodeComputation`, and the emitted values are polynomially bounded
(`encode (prefixSentenceEnum n) ∈ {n, pair 1 n + 1}`), so the obligation is interpreter
programming (deciding canonicity of `n`), not a size obstruction.  The weight emission
is *derived* (`approx_polyRat_of_sentence`), as are the two gate token streams of
`OccamThresholdEmission` (`prefixThresholdSum_polyRat`, `prefixInverseWidth_polyRat`).
Paper node: `thm:ob` -/
structure PrefixMachineComputation where
  sentence_poly : PolySentenceCodes prefixSentenceEnum

/-- The derived weight emission of the operational input.
Paper node: `thm:ob` -/
theorem PrefixMachineComputation.approx_poly (C : PrefixMachineComputation) :
    PolyRatCodes prefixApprox :=
  approx_polyRat_of_sentence C.sentence_poly

/-- The concrete prefix machine presentation: every mathematical field is discharged
here (`kraft` via `kraft_inequality`, coverage, exactness and convergence of the
weights); the fuel-model emission certificates come from the operational input.
Paper node: `thm:ob` -/
def prefixMachinePresentation (C : PrefixMachineComputation) :
    PrefixMachinePresentation prefixKappa where
  sentence := prefixSentenceEnum
  sentence_codes := C.sentence_poly
  approximation := fun _ i => prefixApprox i
  approximation_codes := by
    obtain ⟨c, hc⟩ := C.approx_poly
    exact ⟨_, hc.comp PolyFueled.right⟩
  approximation_nonneg := fun _ i => (prefixApprox_pos i).le
  approximation_le := fun n i => (prefixApprox_eq i).le
  approximation_tendsto := fun i => by
    rw [← prefixApprox_eq]
    exact tendsto_const_nhds
  kraft := prefixKraft
  covers := prefixSentenceEnum_covers

/-- The gate token emission of the concrete machine, transported from the operational
input along the definitional match between `obBase` over the assembled presentation and
`prefixEmitBase`.
Paper node: `thm:ob` -/
def prefixThresholdEmission (C : PrefixMachineComputation) :
    OccamThresholdEmission (prefixMachinePresentation C) where
  threshold_sum_codes := by
    obtain ⟨c, hc⟩ := prefixThresholdSum_polyRat C.approx_poly
    exact ⟨_, hc.of_eq (fun z => by
      simp [prefixEmitBase, obEmitBase, obBase, obCapacity,
        prefixMachinePresentation])⟩
  inverse_width_codes := by
    obtain ⟨c, hc⟩ := prefixInverseWidth_polyRat C.approx_poly
    exact ⟨_, hc.of_eq (fun z => by
      simp [prefixEmitBase, obEmitBase, obBase, obCapacity,
        prefixMachinePresentation])⟩

/-! ## Paper-facing corollaries over the concrete machine -/

/-- Lower Occam bound over the concrete prefix machine: the presentation, threshold
emission, and Kraft budget are all supplied by this file's construction; only the
fuel-model emission programs remain as the operational input.
Paper node: `thm:ob` -/
theorem lic_occam_lower_ofPrefixMachine (C : PrefixMachineComputation)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ K : ℝ, 0 < K ∧ ∀ φ,
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ) →
      K * prefixWeight prefixKappa φ ≤ limitingBelief P φ :=
  lic_occam_lower (prefixMachinePresentation C) (prefixThresholdEmission C) P DP hworld

/-- Occam Bounds over the concrete prefix machine, with the negation compiler
discharged by `prefixNegationCompiler` (overhead 2, proved).
Paper node: `thm:ob` -/
theorem lic_occamBounds_ofPrefixMachine (C : PrefixMachineComputation)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ K : ℝ, 0 < K ∧
      (∀ φ,
        (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ) →
        K * prefixWeight prefixKappa φ ≤ limitingBelief P φ) ∧
      (∀ φ,
        (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds φ) →
        limitingBelief P φ ≤ 1 - K * prefixWeight prefixKappa φ) :=
  lic_occamBounds (prefixMachinePresentation C) (prefixThresholdEmission C)
    prefixNegationCompiler P DP hworld

#print axioms kraft_inequality
#print axioms approx_polyRat_of_sentence
#print axioms sentencePoly_of_invalidBit
#print axioms sentCode_prefix_inj
#print axioms prefixKraft
#print axioms prefixNegationCompiler
#print axioms prefixMachinePresentation
#print axioms lic_occam_lower_ofPrefixMachine
#print axioms lic_occamBounds_ofPrefixMachine

end LogicalInduction
