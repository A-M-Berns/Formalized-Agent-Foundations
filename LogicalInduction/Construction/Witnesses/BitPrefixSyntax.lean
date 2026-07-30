import LogicalInduction.Construction.Witnesses.BoundedEvaluation
import LogicalInduction.Properties.UniversalSemimeasure

/-!
# Concrete Boolean-prefix syntax for `thm:dus`

Domination of the Universal Semimeasure (`thm:dus`) is stated over an abstract
`BitPrefixSentences` presentation.  This file supplies a concrete one: prefix sentences are
literal finite conjunctions over an independent atom family, and the finite-string
enumeration is the total decode-with-empty enumeration induced by the stock `List Bool`
encoding.

Two inputs remain, both conclusion-free.  `IndependentBitAtoms` supplies only finite
compatibility with the deductive stages — it is inhabited (`ordinaryIndependentBitAtoms`).
`BitPrefixCodeComputation` was to supply one program which emits the code of the *actual*
conjunction below with polynomial fuel.

**Verified obstruction (non-vacuity guard).**  That second input is **unsatisfiable**:
`bitPrefixCodeComputation_isEmpty` proves `IsEmpty (BitPrefixCodeComputation I)` for every
atom family `I`.  A `⋏` node costs two nested `Nat.pair`s and a `List Bool` cons costs one,
so along the all-ones strings the prefix sentence's code (`≥ 2 ^ 4 ^ m`) outruns every
polynomial in its own enumeration index (`≤ 5 ^ 2 ^ m`).  Everything below that consumes the
certificate — `bitPrefixSentencesOfIndependentAtoms`,
`lic_domination_universalSemimeasure_ofIndependentAtoms`, and the `_unconditional` `thm:dus`
endpoints in `UnconditionalOverLIA.lean` — is therefore **vacuously true** and carries no
content until the interface is repaired.

Two repairs are open, both larger than a wiring change and neither attempted here:

* **Symbol metering.**  Replace `BitPrefixSentences.prefix_codes`'s whole-value
  `PolySentenceCodes` by the repo's own symbol-metered `RpnSentenceCodes`
  (`Framework/RpnSplice.lean`), whose docstring names precisely this pathology ("deep or
  skewed sentence sequences whose codes are value-exponential in their symbol count").  The
  canonical Polish run of the prefix conjunction is `Θ(m)` tiny tokens, so the certificate
  becomes discharge-able; the cost is migrating the DUS trader's emission chain in
  `Properties/UniversalSemimeasure.lean` from the `PolySegStream` suite to the
  `RpnSpliceStream` mirrors (the ROI layer is already on the latter).
* **Shallow syntax.**  Keep whole-value metering and reparenthesize the prefix conjunction
  so its depth is `O(m / b)` for some `b ≥ 3` (equivalently `O(log m)`), which brings the
  code value back under the index; the cost is a fuel-clocked emitter for the reshaped tree,
  including a decode walk of the `List Bool` index.
-/

namespace LogicalInduction

open LO.Propositional

/-! ### Literal conjunctions and their exact semantics -/

/-- The positive or negative literal selected by one prefix bit. -/
def bitPrefixLiteral (atom : ℕ → Sentence) (k : ℕ) (b : Bool) : Sentence :=
  if b then atom k else ∼atom k

/-- The concrete prefix sentence: one literal for every position, conjoined in index
order.  `List.conj` makes the empty prefix the true sentence `⊤`. -/
def bitPrefixSentence (atom : ℕ → Sentence) (σ : List Bool) : Sentence :=
  (List.ofFn fun k : Fin σ.length ↦ bitPrefixLiteral atom k (σ.get k)).conj

@[simp] theorem PCWorld.holds_bitPrefixLiteral
    (v : PCWorld) (atom : ℕ → Sentence) (k : ℕ) (b : Bool) :
    v.Holds (bitPrefixLiteral atom k b) ↔ (v.Holds (atom k) ↔ b = true) := by
  cases b <;>
    simp [bitPrefixLiteral, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]

/-- Exact Boolean semantics of the literal conjunction, including the empty prefix. -/
@[simp] theorem PCWorld.holds_bitPrefixSentence
    (v : PCWorld) (atom : ℕ → Sentence) (σ : List Bool) :
    v.Holds (bitPrefixSentence atom σ) ↔
      ∀ k : Fin σ.length, (v.Holds (atom k) ↔ σ.get k = true) := by
  have hlist (l : List Sentence) :
      LO.Propositional.Formula.Boolean.val v l.conj ↔
        ∀ φ ∈ l, LO.Propositional.Formula.Boolean.val v φ := by
    induction l with
    | nil => simp [List.conj, LO.Propositional.Formula.Boolean.val]
    | cons φ l ih =>
        simp [List.conj, LO.Propositional.Formula.Boolean.val, ih]
  rw [bitPrefixSentence, show v.Holds
      (List.ofFn fun k : Fin σ.length ↦
        bitPrefixLiteral atom k (σ.get k)).conj =
      LO.Propositional.Formula.Boolean.val v
        (List.ofFn fun k : Fin σ.length ↦
          bitPrefixLiteral atom k (σ.get k)).conj from rfl]
  rw [hlist, List.forall_mem_ofFn_iff]
  apply forall_congr'
  intro k
  exact v.holds_bitPrefixLiteral atom k (σ.get k)

/-! ### Concrete total enumeration -/

/-- Decode a stock `List Bool` code, using the empty string for malformed codes. -/
def bitStringEnumeration (i : ℕ) : List Bool :=
  (Encodable.decode (α := List Bool) i).getD []

lemma bitStringEnumeration_covers (σ : List Bool) :
    ∃ i, bitStringEnumeration i = σ := by
  refine ⟨Encodable.encode σ, ?_⟩
  simp [bitStringEnumeration, Encodable.encodek]

/-! ### Non-vacuity of the independence premise -/

/-- The constantly empty deductive process used to witness that finite atom independence
is a genuine, inhabited premise. -/
def emptyBitDeductiveProcess : DeductiveProcess where
  D := fun _ ↦ ∅
  mono := fun _ φ hφ ↦ by simp at hφ

/-- Ordinary propositional atoms are independently realizable over the constantly empty
deductive process. -/
def ordinaryIndependentBitAtoms : IndependentBitAtoms emptyBitDeductiveProcess where
  atom := LO.Propositional.Formula.atom
  realizable := by
    intro n f
    refine ⟨fun a ↦ f a = true, ?_, ?_⟩
    · intro φ hφ
      simp [emptyBitDeductiveProcess] at hφ
    · intro k
      rfl

lemma independentBitAtoms_nonempty :
    ∃ DP : DeductiveProcess, Nonempty (IndependentBitAtoms DP) :=
  ⟨emptyBitDeductiveProcess, ⟨ordinaryIndependentBitAtoms⟩⟩

/-! ### Operational certificate and public constructor -/

/-- Compact operational input for polynomial naming of the concrete prefix conjunction.
The program is indexed by the same enumeration index consumed by the DUS trader.

**Uninhabited — see `bitPrefixCodeComputation_isEmpty` below.**  `PolyFueled` requires the
emitted *code value* to be polynomially bounded in the enumeration index, and the literal
conjunction's Gödel code is not: each `⋏` node costs two nested `Nat.pair`s (a fourth power)
while each `List Bool` cons costs one (a square), so the sentence code of the length-`m`
prefix is `≥ 2 ^ 4 ^ m` against a list code `≤ 5 ^ 2 ^ m`.  Every consumer of this structure
is therefore vacuous; the repair options are recorded in the file docstring above.
Paper node: `thm:dus`, `thm:strict` -/
structure BitPrefixCodeComputation {DP : DeductiveProcess}
    (I : IndependentBitAtoms DP) where
  code : Nat.Partrec.Code
  code_poly : PolyFueled code (fun i ↦
    Encodable.encode (bitPrefixSentence I.atom (bitStringEnumeration i)))

/-! ### The whole-value emission premise is unsatisfiable

The non-vacuity guard, run in the negative direction: the whole-value certificate
`BitPrefixCodeComputation` demanded above has **no inhabitant**, for any atom family over any
deductive process.  `PolyFueled` bundles `IsPolyBounded` of the computed function itself, so
it suffices to refute the output bound.

`Nat.pair x y ≥ y * y` makes the conjunction code grow with exponent `4 ^ m` in the prefix
length `m`, whereas the stock `List Bool` code — the enumeration index the bound is measured
against — grows only with exponent `2 ^ m`.  The gap doubles the exponent per bit, so no
polynomial covers it.  This is exactly the whole-value/symbol-metered mismatch documented at
`RpnSentenceCodes` (`Framework/RpnSplice.lean`), which meters symbols instead of the pair-code
value and is the interface a repair should use. -/

private lemma sq_le_pair (x y : ℕ) : y * y ≤ Nat.pair x y := by
  rw [Nat.pair]
  split
  · exact Nat.le_add_right _ _
  · next h =>
      have hxy : y ≤ x := Nat.le_of_not_lt h
      calc y * y ≤ x * x := Nat.mul_le_mul hxy hxy
        _ ≤ x * x + x + y := by omega

/-- A right-nested conjunction of `m` sentences has Gödel code at least `2 ^ 4 ^ m`, whatever
its conjuncts are: every `⋏` node is two nested pairings, and each pairing squares. -/
lemma two_pow_le_encode_conj (l : List Sentence) :
    2 ^ (4 ^ l.length) ≤ Encodable.encode l.conj := by
  induction l with
  | nil => decide
  | cons a l ih =>
      have hrw : Encodable.encode (a :: l).conj
          = Nat.pair 3 (Nat.pair (Encodable.encode a) (Encodable.encode l.conj)) + 1 := rfl
      set S := Encodable.encode l.conj with hS
      have h1 : S * S ≤ Nat.pair (Encodable.encode a) S := sq_le_pair _ _
      have h2 : (S * S) * (S * S) ≤ Nat.pair 3 (Nat.pair (Encodable.encode a) S) :=
        le_trans (Nat.mul_le_mul h1 h1) (sq_le_pair 3 _)
      have hexp : 4 ^ (l.length + 1)
          = 4 ^ l.length + 4 ^ l.length + (4 ^ l.length + 4 ^ l.length) := by
        rw [pow_succ]; ring
      have h4 : 2 ^ (4 ^ (l.length + 1)) ≤ (S * S) * (S * S) := by
        simp only [hexp, pow_add]
        exact Nat.mul_le_mul (Nat.mul_le_mul ih ih) (Nat.mul_le_mul ih ih)
      rw [hrw, List.length_cons]
      omega

/-- The stock `List Bool` code of the all-ones string of length `m` is below `5 ^ 2 ^ m`:
one pairing, hence one squaring, per bit. -/
lemma encode_replicate_true_le (m : ℕ) :
    Encodable.encode (List.replicate m true) + 3 ≤ 5 ^ 2 ^ m := by
  induction m with
  | zero => decide
  | succ m ih =>
      have hcons : Encodable.encode (List.replicate (m + 1) true)
          = Nat.pair 1 (Encodable.encode (List.replicate m true)) + 1 := rfl
      set E := Encodable.encode (List.replicate m true) with hE
      have hstep : Nat.pair 1 E + 1 + 3 ≤ (E + 3) * (E + 3) := by
        rw [Nat.pair]
        split
        · next h => nlinarith
        · next h => nlinarith
      calc Encodable.encode (List.replicate (m + 1) true) + 3
          ≤ (E + 3) * (E + 3) := by rw [hcons]; exact hstep
        _ ≤ (5 ^ 2 ^ m) * (5 ^ 2 ^ m) := Nat.mul_le_mul ih ih
        _ = 5 ^ 2 ^ (m + 1) := by rw [← pow_add, pow_succ]; ring_nf

/-- **The whole-value prefix-code bound fails.**  Reading the all-ones string of length `m`
off its own stock code puts a sentence of code `≥ 2 ^ 4 ^ m` at an index `≤ 5 ^ 2 ^ m`, and
`4 ^ m` outruns every `a * (n + 1) ^ k + a`. -/
lemma not_isPolyBounded_bitPrefixSentence_codes (atom : ℕ → Sentence) :
    ¬ IsPolyBounded
      (fun i ↦ Encodable.encode (bitPrefixSentence atom (bitStringEnumeration i))) := by
  rintro ⟨a, k, hk⟩
  obtain ⟨m, hm⟩ : ∃ m, m = a + 3 * k + 4 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = Encodable.encode (List.replicate m true) := ⟨_, rfl⟩
  have hdec : bitStringEnumeration E = List.replicate m true := by
    rw [hE]
    simp [bitStringEnumeration, Encodable.encodek]
  have hlen : (List.ofFn fun j : Fin (List.replicate m true).length ↦
      bitPrefixLiteral atom j ((List.replicate m true).get j)).length = m := by
    simp
  have hlow : 2 ^ 4 ^ m ≤
      Encodable.encode (bitPrefixSentence atom (List.replicate m true)) := by
    have h := two_pow_le_encode_conj (List.ofFn fun j : Fin (List.replicate m true).length ↦
      bitPrefixLiteral atom j ((List.replicate m true).get j))
    rw [hlen] at h
    exact h
  have hup := hk E
  simp only [hdec] at hup
  have hE1 : E + 1 ≤ 5 ^ 2 ^ m := by
    have h := encode_replicate_true_le m
    omega
  have hchain : 2 ^ 4 ^ m ≤ a * (5 ^ 2 ^ m) ^ k + a := by
    refine le_trans hlow (le_trans hup ?_)
    have hp : (E + 1) ^ k ≤ (5 ^ 2 ^ m) ^ k := Nat.pow_le_pow_left hE1 k
    exact Nat.add_le_add_right (Nat.mul_le_mul_left a hp) a
  have hpow5 : (5 ^ 2 ^ m) ^ k ≤ 2 ^ (3 * (k * 2 ^ m)) := by
    calc (5 ^ 2 ^ m) ^ k = 5 ^ (2 ^ m * k) := by rw [← pow_mul]
      _ ≤ 8 ^ (2 ^ m * k) := Nat.pow_le_pow_left (by norm_num) _
      _ = 2 ^ (3 * (k * 2 ^ m)) := by
          rw [show (8:ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
          ring_nf
  have hfin : 2 ^ 4 ^ m ≤ 2 ^ (a + 2 + 3 * (k * 2 ^ m)) := by
    have hone : 1 ≤ (5 ^ 2 ^ m) ^ k := Nat.one_le_pow _ _ (by positivity)
    have h1 : a * (5 ^ 2 ^ m) ^ k + a ≤ (2 * (a + 1)) * (5 ^ 2 ^ m) ^ k := by nlinarith
    have h2 : 2 * (a + 1) ≤ 2 ^ (a + 2) := by
      have hlt := Nat.lt_two_pow_self (n := a + 1)
      calc 2 * (a + 1) ≤ 2 * 2 ^ (a + 1) := by omega
        _ = 2 ^ (a + 2) := by ring
    calc 2 ^ 4 ^ m ≤ (2 * (a + 1)) * (5 ^ 2 ^ m) ^ k := le_trans hchain h1
      _ ≤ 2 ^ (a + 2) * 2 ^ (3 * (k * 2 ^ m)) := Nat.mul_le_mul h2 hpow5
      _ = 2 ^ (a + 2 + 3 * (k * 2 ^ m)) := by rw [← pow_add]
  have hexp : 4 ^ m ≤ a + 2 + 3 * (k * 2 ^ m) :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp hfin
  have h2m : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  have h4m : 4 ^ m = 2 ^ m * 2 ^ m := by
    rw [show (4:ℕ) = 2 * 2 by norm_num, mul_pow]
  have hbig : (a + 3 * k + 4) * 2 ^ m ≤ 2 ^ m * 2 ^ m :=
    Nat.mul_le_mul_right _ (by omega)
  have hone : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  nlinarith [hexp, h4m, hbig, hone]

/-- **The prefix-code certificate has no inhabitant.**  Consequently every statement taking a
`BitPrefixCodeComputation` — `bitPrefixSentencesOfIndependentAtoms` and everything downstream
of it — is vacuous, and the interface must be repaired (symbol-metered `RpnSentenceCodes`, or
a prefix syntax of logarithmic depth) before those statements carry content. -/
lemma bitPrefixCodeComputation_isEmpty {DP : DeductiveProcess} (I : IndependentBitAtoms DP) :
    IsEmpty (BitPrefixCodeComputation I) := by
  refine ⟨fun C ↦ ?_⟩
  obtain ⟨b, -, hpoly, -⟩ := C.code_poly
  exact not_isPolyBounded_bitPrefixSentence_codes I.atom hpoly

/-- Construct the complete prefix presentation from independent atoms and a compact
program for the actual literal conjunction code.

**Vacuous:** its second argument is uninhabited (`bitPrefixCodeComputation_isEmpty`), so this
constructor has no applications and produces no `BitPrefixSentences` witness.
Paper node: `thm:dus` -/
def bitPrefixSentencesOfIndependentAtoms
    {DP : DeductiveProcess} (I : IndependentBitAtoms DP)
    (C : BitPrefixCodeComputation I) : BitPrefixSentences DP where
  atom := I.atom
  prefixSentence := bitPrefixSentence I.atom
  enumeration := bitStringEnumeration
  enumeration_covers := bitStringEnumeration_covers
  prefix_codes := ⟨C.code, C.code_poly⟩
  holds_prefix := fun v σ ↦ PCWorld.holds_bitPrefixSentence v I.atom σ
  realizable := I.realizable

/-- Domination of the universal semimeasure with the opaque `BitPrefixSentences` argument
discharged by the concrete Boolean-prefix constructor.  The semimeasure's from-below
approximation and its threshold emission remain caller inputs.

**Vacuous:** the hypothesis `C` is uninhabited (`bitPrefixCodeComputation_isEmpty`).
Paper node: `thm:dus` -/
theorem lic_domination_universalSemimeasure_ofIndependentAtoms
    {DP : DeductiveProcess}
    (I : IndependentBitAtoms DP) (C : BitPrefixCodeComputation I)
    {M : LowerSemicomputableContinuousSemimeasure}
    (A : DUSApproximationPresentation M
      (bitPrefixSentencesOfIndependentAtoms I C))
    (emit : DUSThresholdEmission A)
    (P : History) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ,
      K * M.mass σ ≤ limitingBelief P
        (bitPrefixSentence I.atom σ) :=
  lic_domination_universalSemimeasure A emit P hworld

#print axioms PCWorld.holds_bitPrefixSentence
#print axioms bitStringEnumeration_covers
#print axioms two_pow_le_encode_conj
#print axioms encode_replicate_true_le
#print axioms not_isPolyBounded_bitPrefixSentence_codes
#print axioms bitPrefixCodeComputation_isEmpty
#print axioms ordinaryIndependentBitAtoms
#print axioms independentBitAtoms_nonempty
#print axioms bitPrefixSentencesOfIndependentAtoms
#print axioms lic_domination_universalSemimeasure_ofIndependentAtoms

end LogicalInduction
