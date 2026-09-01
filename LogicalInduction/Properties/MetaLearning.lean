/-
# Trust in Consistency and Reasoning about Halting — §4.9–4.10

`thm:pac`, `thm:pazfc`, `thm:incons` (trust in consistency); `thm:halts`, `thm:loops`,
`thm:dontwait` (halting patterns).

The paper derives these from Provability Induction plus the assumption that the background
theory represents computations.  The sentences here are propositional rather than
first-order Gödel syntax, so the representation step is exposed as a narrow interface.  Its
fields mention only sentence emission and eventual theoremhood/refutability; they never
mention market prices or any desired asymptotic conclusion.
-/
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Framework.WriteOut

namespace LogicalInduction

open Filter Topology

/-- A uniformly emitted sentence family representing a semidecidable predicate.  When the
external computation is true, its representing sentence eventually occurs in the deductive
process.  This is the exact propositional boundary used for halting and inconsistency.
Paper node: `thm:pac`, `thm:pazfc`, `thm:incons`, `thm:halts`, `thm:loops`, `thm:dontwait` -/
structure RepresentedSemidecidableClaims (DP : DeductiveProcess) (truth : ℕ → Prop) where
  sentence : ℕ → Sentence
  sentence_poly : BigSentenceCodes sentence
  provable_of_true : ∀ n, truth n → ∃ k, sentence n ∈ DP.D k

/-- A uniformly emitted sentence family representing a decidable computation.  In addition
to positive representation, a false computation eventually yields the negated sentence.
Finite proof searches and bounded machine simulations have this form.
Paper node: `thm:pac`, `thm:pazfc`, `thm:incons`, `thm:halts`, `thm:loops`, `thm:dontwait` -/
structure RepresentedDecidableClaims (DP : DeductiveProcess) (truth : ℕ → Prop)
    extends RepresentedSemidecidableClaims DP truth where
  disprovable_of_false : ∀ n, ¬truth n → ∃ k, (∼sentence n) ∈ DP.D k

/-- Halting of one `Nat.Partrec.Code` machine on one natural-number input. -/
def CodeHalts (machine : Nat.Partrec.Code) (input : ℕ) : Prop :=
  (machine.eval input).Dom

/-- Termination within a fixed interpreter clock.  Unlike unbounded halting, this predicate
is decidable and is the computation represented in `thm:dontwait`. -/
def CodeHaltsWithin (machine : Nat.Partrec.Code) (input steps : ℕ) : Prop :=
  (Nat.Partrec.Code.evaln steps machine input).isSome = true

/-- The emitted “`⌜Θ′ₙ⌝` is inconsistent” family.  One sentence sequence, not two: the paper
defines `⌜Θ′⌝ is inconsistent` as the *negation* of `⌜Θ′⌝ is consistent` (tex:1863-1866), so
the consistency family is recovered syntactically by `consistencySentence` below rather than
carried as an independent field.  The earlier two-family shape existed to avoid assuming a
syntactic negation on the abstract `Sentence` type; `Sentence` is Foundation's propositional
`Formula`, which has one, so the reason no longer holds.
Paper node: `thm:incons` -/
structure InconsistentTheoryClaims (DP : DeductiveProcess) (inconsistent : ℕ → Prop) where
  inconsistencySentence : ℕ → Sentence
  inconsistency_poly : BigSentenceCodes inconsistencySentence
  inconsistency_provable : ∀ n, inconsistent n →
    ∃ k, inconsistencySentence n ∈ DP.D k

/-- **The paper's “`⌜Θ′ₙ⌝` is consistent”**: the negation of the day-`n` inconsistency
sentence (tex:1863-1866). -/
def InconsistentTheoryClaims.consistencySentence {DP : DeductiveProcess}
    {inconsistent : ℕ → Prop} (R : InconsistentTheoryClaims DP inconsistent) (n : ℕ) :
    Sentence :=
  ∼R.inconsistencySentence n

/-- **Provability induction at the negated sentence.**  `lic_provind_false` asks for `∼ψ` to
enter the completed theory; when `ψ` is itself a negation `∼φ` of a *theorem*, that would ask
for `∼∼φ`, which the paper's prime decomposition never emits.  The price still goes to zero,
for the same reason and by the same argument: in a world consistent with the stage, `φ` holds,
so `∼φ` does not, so every sampled payout of `∼φ` is `0`. -/
private lemma provind_neg_false (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
    (hthm : ∀ n, ∃ k, φ n ∈ DP.D k)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (∼φ n)) ≈ₙ fun _ => 0 := by
  let hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1 :=
    fun n χ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n χ
  have hψpoly := AffineCombination.sentenceAffine_polySequence (fun n => ∼φ n) hφ.neg
  have hψeq := hψpoly.affine_provind_theory_eq P DP
    (AffineCombination.sentenceAffine_bounded _ P hP)
    ⟨1, fun n => by simp⟩ hworld 0 (fun n v hv => by
      obtain ⟨k, hk⟩ := hthm n
      have hpos := hv k (φ n) hk
      have hfalse : ¬v.Holds (∼φ n) := fun h => (PCWorld.holds_neg v (φ n)).mp h hpos
      simp [AffineCombination.sentenceAffine, AffineCombination.value,
        PCWorld.payout, hfalse])
  simpa using hψeq

/-- **Belief in Finitistic Consistency** (`thm:pac`), at the propositional computation-
representation boundary.  `consistentWithin n` is the truth of the finite proof search
named on day `n`; its representing syntax may compactly contain a fixed arbitrary
computable function rather than evaluating that function in polynomial time.

The representation premise is the **semidecidable** one.  Every day's claim is true here
(`hconsistent`), so only the positive half of a decidable representation is ever consumed —
the negative field `disprovable_of_false` of `RepresentedDecidableClaims` would be
unreachable.  Callers holding a decidable bundle pass its
`.toRepresentedSemidecidableClaims` projection; keeping the weaker premise is what makes
that visible in the statement rather than only in the proof.
Paper node: `thm:pac` -/
theorem lic_belief_finitistic_consistency
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (consistentWithin : ℕ → Prop)
    (R : RepresentedSemidecidableClaims DP consistentWithin)
    (hconsistent : ∀ n, consistentWithin n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (R.sentence n)) ≈ₙ fun _ => 1 :=
  lic_provind_true P DP R.sentence R.sentence_poly
    (fun n => R.provable_of_true n (hconsistent n)) hworld

/-- **Disbelief in Inconsistent Theories** (`thm:incons`): timely belief in each emitted
inconsistency sentence and, therefore, timely disbelief in its negation — the paper's
consistency sentence.  The second conjunct costs no further representation premise; it is the
first one read through the market's own valuation of a negation.

*What this layer is.*  This is the **abstract boundary**, not the content: `inconsistent`
and `hall` are carried only so that the `InconsistentTheoryClaims` bundle can be indexed by
the property its witness is required to establish, and the proof consumes nothing but
`R.inconsistency_provable` at every day.  The premise parameter is therefore not eliminable
without dissolving the bundle's index — and it should not be: what makes `thm:incons` a
theorem about *theories* rather than about an arbitrary emitted sentence family lives
entirely in the witnesses (`representedInconsistentTheoryClaims` and the applied endpoints
in `Construction/Witnesses/ComputationRepresented.lean`), where `inconsistent n` is
instantiated at `¬Entailment.Consistent (theoryOf (m n))` — the freestanding day-theory
enumerated by the day's machine, with no base theory anywhere — and discharged.
Paper node: `thm:incons` -/
theorem lic_disbelief_inconsistent_theories
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (inconsistent : ℕ → Prop) (R : InconsistentTheoryClaims DP inconsistent)
    (hall : ∀ n, inconsistent n)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ((fun n => P n (R.inconsistencySentence n)) ≈ₙ fun _ => 1) ∧
      ((fun n => P n (R.consistencySentence n)) ≈ₙ fun _ => 0) :=
  ⟨lic_provind_true P DP R.inconsistencySentence R.inconsistency_poly
      (fun n => R.inconsistency_provable n (hall n)) hworld,
    provind_neg_false P DP R.inconsistencySentence R.inconsistency_poly
      (fun n => R.inconsistency_provable n (hall n)) hworld⟩

/-- **Learning of Halting Patterns** (`thm:halts`) for polynomially named machine/input
sequences.  Machine runtime is unrestricted: only the representing sentence sequence must
be polynomially emitted.
Paper node: `thm:halts` -/
theorem lic_learns_halting_patterns
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (R : RepresentedSemidecidableClaims DP
      (fun n => CodeHalts (machines n) (inputs n)))
    (hhalts : ∀ n, CodeHalts (machines n) (inputs n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (R.sentence n)) ≈ₙ fun _ => 1 :=
  lic_provind_true P DP R.sentence R.sentence_poly
    (fun n => R.provable_of_true n (hhalts n)) hworld

/-- **Learning of Provable Non-Halting Patterns** (`thm:loops`).  “Provably fails to
halt” is rendered directly as eventual occurrence of the negated represented halting
sentence; no semantic completeness assumption for arbitrary non-halting machines is used.
Paper node: `thm:loops` -/
theorem lic_learns_provable_nonhalting_patterns
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (machines : ℕ → Nat.Partrec.Code) (inputs : ℕ → ℕ)
    (R : RepresentedSemidecidableClaims DP
      (fun n => CodeHalts (machines n) (inputs n)))
    (hloops : ∀ n, ∃ k, (∼R.sentence n) ∈ DP.D k)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (R.sentence n)) ≈ₙ fun _ => 0 :=
  lic_provind_false P DP R.sentence R.sentence_poly hloops hworld

/-- **Learning not to Anticipate Halting** (`thm:dontwait`).  The compact sentence may
refer to a fixed arbitrary computable horizon program; its day-indexed syntax is what the
polynomial code field certifies.  Actual non-halting makes every bounded claim false, and
decidable computation representation supplies its eventual refutation.
Paper node: `thm:dontwait` -/
theorem lic_does_not_anticipate_halting
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (machines : ℕ → Nat.Partrec.Code) (inputs horizons : ℕ → ℕ)
    (R : RepresentedDecidableClaims DP
      (fun n => CodeHaltsWithin (machines n) (inputs n) (horizons n)))
    (hnever : ∀ n, ¬CodeHalts (machines n) (inputs n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (R.sentence n)) ≈ₙ fun _ => 0 := by
  apply lic_provind_false P DP R.sentence R.sentence_poly _ hworld
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
#print axioms lic_disbelief_inconsistent_theories
#print axioms lic_learns_halting_patterns
#print axioms lic_learns_provable_nonhalting_patterns
#print axioms lic_does_not_anticipate_halting

end LogicalInduction
