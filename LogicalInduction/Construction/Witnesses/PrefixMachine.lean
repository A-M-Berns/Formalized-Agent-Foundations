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

/-! ## Residual operational input and the assembled boundary -/

/-- Compact operational input for the concrete prefix machine: the fuel-model programs
emitting the enumerated sentence codes, the exact rational weights, and the two derived
gate token streams.  These are the only fields of the Occam boundary not discharged by
this file; they are conclusion-free emission certificates in the style of
`BitPrefixCodeComputation`, and the corresponding values are polynomially bounded (the
weights' denominators are `2^κ ≤ poly(i)`), so the obligation is interpreter
programming, not a size obstruction.
Paper node: `thm:ob` -/
structure PrefixMachineComputation where
  sentence_poly : PolySentenceCodes prefixSentenceEnum
  approx_poly : PolyRatCodes prefixApprox
  threshold_sum_poly : PolyRatCodes (fun z => prefixEmitBase z + prefixEmitBase z)
  inverse_width_poly : PolyRatCodes (fun z => 1 / prefixEmitBase z)

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
    obtain ⟨c, hc⟩ := C.threshold_sum_poly
    exact ⟨_, hc.of_eq (fun z => by
      simp [prefixEmitBase, obEmitBase, obBase, obCapacity,
        prefixMachinePresentation])⟩
  inverse_width_codes := by
    obtain ⟨c, hc⟩ := C.inverse_width_poly
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
#print axioms sentCode_prefix_inj
#print axioms prefixKraft
#print axioms prefixNegationCompiler
#print axioms prefixMachinePresentation
#print axioms lic_occam_lower_ofPrefixMachine
#print axioms lic_occamBounds_ofPrefixMachine

end LogicalInduction
