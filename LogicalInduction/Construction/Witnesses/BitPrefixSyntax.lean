import LogicalInduction.Construction.Witnesses.M7Witnesses
import LogicalInduction.Properties.UniversalSemimeasure

/-!
# Concrete Boolean-prefix syntax for Domination of the Universal Semimeasure

This file constructs `M7-DUS-PREFIX-SYNTAX`.  Prefix sentences are literal finite
conjunctions over an independent atom family, and the finite-string enumeration is the
total decode-with-empty enumeration induced by the stock `List Bool` encoding.

The two residual inputs are honest and conclusion-free.  `IndependentBitAtoms` supplies
only finite compatibility with the deductive stages.  `BitPrefixCodeComputation` supplies
one program which emits the code of the *actual* conjunction below with polynomial fuel;
ordinary primitive recursiveness alone would not justify that whole-number bound.
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
Paper node: `thm:dus`, `thm:strict` -/
structure BitPrefixCodeComputation {DP : DeductiveProcess}
    (I : IndependentBitAtoms DP) where
  code : Nat.Partrec.Code
  code_poly : PolyFueled code (fun i ↦
    Encodable.encode (bitPrefixSentence I.atom (bitStringEnumeration i)))

/-- Construct the complete prefix presentation from independent atoms and a compact
program for the actual literal conjunction code.
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
discharged by the concrete Boolean-prefix constructor.  The approximation and threshold
emission premises remain explicit (`M7-DUS-APPROX`).
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
#print axioms ordinaryIndependentBitAtoms
#print axioms independentBitAtoms_nonempty
#print axioms bitPrefixSentencesOfIndependentAtoms
#print axioms lic_domination_universalSemimeasure_ofIndependentAtoms

end LogicalInduction
