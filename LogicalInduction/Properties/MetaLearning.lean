/-
# Metamathematical and halting-pattern consequences

The paper derives these nodes from Provability Induction plus the assumption that the
background theory represents computations.  This repository has propositional sentences
rather than first-order Gödel syntax, so the representation step is exposed as a narrow
interface.  Its fields mention only sentence emission and eventual theoremhood/refutability;
they never mention market prices or any desired asymptotic conclusion.
-/
import LogicalInduction.Properties.AffineCoherence

namespace LogicalInduction

open Filter Topology

/-- A uniformly emitted sentence family representing a semidecidable predicate.  When the
external computation is true, its representing sentence eventually occurs in the deductive
process.  This is the exact propositional boundary used for halting and inconsistency.  Paper nodes: the §2.1 representation premises for `thm:pac`–`thm:dontwait`. -/
structure RepresentedSemidecidableClaims (DP : DeductiveProcess) (truth : ℕ → Prop) where
  sentence : ℕ → Sentence
  sentence_poly : PolySentenceCodes sentence
  provable_of_true : ∀ n, truth n → ∃ k, sentence n ∈ DP.D k

/-- A uniformly emitted sentence family representing a decidable computation.  In addition
to positive representation, a false computation eventually yields the negated sentence.
Finite proof searches and bounded machine simulations have this form.  Paper nodes: the §2.1 representation premises for `thm:pac`–`thm:dontwait`. -/
structure RepresentedDecidableClaims (DP : DeductiveProcess) (truth : ℕ → Prop)
    extends RepresentedSemidecidableClaims DP truth where
  disprovable_of_false : ∀ n, ¬truth n → ∃ k, (∼sentence n) ∈ DP.D k

/-- Halting of one repository machine code on one natural-number input. -/
def CodeHalts (machine : Nat.Partrec.Code) (input : ℕ) : Prop :=
  (machine.eval input).Dom

/-- Termination within a fixed interpreter clock.  Unlike unbounded halting, this predicate
is decidable and is the computation represented in `thm:dontwait`. -/
def CodeHaltsWithin (machine : Nat.Partrec.Code) (input steps : ℕ) : Prop :=
  (Nat.Partrec.Code.evaln steps machine input).isSome = true

/-- The two separately emitted sentences used for an inconsistent theory: “inconsistent”
is eventually proved when the finite contradiction search succeeds, while “consistent” is
then refuted.  Keeping both sequences explicit avoids assuming a syntactic-negation law that
the repository's abstract `Sentence` representation does not provide. -/
structure InconsistentTheoryClaims (DP : DeductiveProcess) (inconsistent : ℕ → Prop) where
  inconsistencySentence : ℕ → Sentence
  consistencySentence : ℕ → Sentence
  inconsistency_poly : PolySentenceCodes inconsistencySentence
  consistency_poly : PolySentenceCodes consistencySentence
  inconsistency_provable : ∀ n, inconsistent n →
    ∃ k, inconsistencySentence n ∈ DP.D k
  consistency_disprovable : ∀ n, inconsistent n →
    ∃ k, (∼consistencySentence n) ∈ DP.D k

/-- **Belief in Finitistic Consistency** (`thm:pac`), at the propositional computation-
representation boundary.  `consistentWithin n` is the truth of the finite proof search
named on day `n`; its representing syntax may compactly contain a fixed arbitrary
computable function rather than evaluating that function in polynomial time. -/
theorem lic_belief_finitistic_consistency
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (consistentWithin : ℕ → Prop)
    (R : RepresentedDecidableClaims DP consistentWithin)
    (hconsistent : ∀ n, consistentWithin n)
    (hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (R.sentence n)) ≈ₙ fun _ => 1 :=
  lic_provind_true P DP R.sentence R.sentence_poly
    (fun n => R.provable_of_true n (hconsistent n)) hP hworld

/-- **Belief in the Consistency of a Stronger Theory** (`thm:pazfc`).  The logical-
induction argument is identical to `thm:pac`; the distinction is carried by the supplied
finite-consistency predicate and its concrete representation witness. -/
theorem lic_belief_stronger_theory_consistency
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (strongerConsistentWithin : ℕ → Prop)
    (R : RepresentedDecidableClaims DP strongerConsistentWithin)
    (hconsistent : ∀ n, strongerConsistentWithin n)
    (hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (R.sentence n)) ≈ₙ fun _ => 1 :=
  lic_provind_true P DP R.sentence R.sentence_poly
    (fun n => R.provable_of_true n (hconsistent n)) hP hworld

/-- **Disbelief in Inconsistent Theories** (`thm:incons`): timely belief in each emitted
inconsistency sentence and timely disbelief in its separately emitted consistency sentence. -/
theorem lic_disbelief_inconsistent_theories
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (inconsistent : ℕ → Prop) (R : InconsistentTheoryClaims DP inconsistent)
    (hall : ∀ n, inconsistent n)
    (hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ((fun n => P n (R.inconsistencySentence n)) ≈ₙ fun _ => 1) ∧
      ((fun n => P n (R.consistencySentence n)) ≈ₙ fun _ => 0) :=
  ⟨lic_provind_true P DP R.inconsistencySentence R.inconsistency_poly
      (fun n => R.inconsistency_provable n (hall n)) hP hworld,
    lic_provind_false P DP R.consistencySentence R.consistency_poly
      (fun n => R.consistency_disprovable n (hall n)) hP hworld⟩

/-- **Learning of Halting Patterns** (`thm:halts`) for polynomially named repository
machine/input sequences.  Machine runtime is unrestricted: only the representing sentence
sequence must be polynomially emitted. -/
theorem lic_learns_halting_patterns
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (R : RepresentedSemidecidableClaims DP
      (fun n => CodeHalts (machines n) (inputs n)))
    (hhalts : ∀ n, CodeHalts (machines n) (inputs n))
    (hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (R.sentence n)) ≈ₙ fun _ => 1 :=
  lic_provind_true P DP R.sentence R.sentence_poly
    (fun n => R.provable_of_true n (hhalts n)) hP hworld

/-- **Learning of Provable Non-Halting Patterns** (`thm:loops`).  “Provably fails to
halt” is rendered directly as eventual occurrence of the negated represented halting
sentence; no semantic completeness assumption for arbitrary non-halting machines is used. -/
theorem lic_learns_provable_nonhalting_patterns
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (R : RepresentedSemidecidableClaims DP
      (fun n => CodeHalts (machines n) (inputs n)))
    (hloops : ∀ n, ∃ k, (∼R.sentence n) ∈ DP.D k)
    (hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (R.sentence n)) ≈ₙ fun _ => 0 :=
  lic_provind_false P DP R.sentence R.sentence_poly hloops hP hworld

/-- **Learning not to Anticipate Halting** (`thm:dontwait`).  The compact sentence may
refer to a fixed arbitrary computable horizon program; its day-indexed syntax is what the
polynomial code field certifies.  Actual non-halting makes every bounded claim false, and
decidable computation representation supplies its eventual refutation. -/
theorem lic_does_not_anticipate_halting
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (machines : ℕ → Nat.Partrec.Code) (inputs horizons : ℕ → ℕ)
    (R : RepresentedDecidableClaims DP
      (fun n => CodeHaltsWithin (machines n) (inputs n) (horizons n)))
    (hnever : ∀ n, ¬CodeHalts (machines n) (inputs n))
    (hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (R.sentence n)) ≈ₙ fun _ => 0 := by
  apply lic_provind_false P DP R.sentence R.sentence_poly _ hP hworld
  intro n
  apply R.disprovable_of_false n
  intro hbounded
  obtain ⟨out, hout⟩ : ∃ out, Nat.Partrec.Code.evaln (horizons n)
      (machines n) (inputs n) = some out := by
    apply Option.isSome_iff_exists.mp
    simpa [CodeHaltsWithin] using hbounded
  apply hnever n
  rw [CodeHalts]
  rw [Part.dom_iff_mem]
  exact ⟨out, Nat.Partrec.Code.evaln_sound (by simpa using hout)⟩

#print axioms lic_belief_finitistic_consistency
#print axioms lic_belief_stronger_theory_consistency
#print axioms lic_disbelief_inconsistent_theories
#print axioms lic_learns_halting_patterns
#print axioms lic_learns_provable_nonhalting_patterns
#print axioms lic_does_not_anticipate_halting

end LogicalInduction
