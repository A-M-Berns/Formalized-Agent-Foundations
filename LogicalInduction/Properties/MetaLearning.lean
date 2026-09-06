import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Framework.Emission.WriteOut

/-!
# Trust in Consistency and Reasoning about Halting

Renders §4.9 *Trust in Consistency* — `thm:pac`, `thm:incons` — and §4.10 *Reasoning about
Halting* — `thm:halts`, `thm:loops`, `thm:dontwait`. The module also supplies the
representation interfaces the `thm:pazfc` lane consumes; that endpoint itself is
`lic_belief_stronger_theory_consistency_unconditional` in
`Construction/Knowledge/Endpoints.lean`.

The paper derives these results from Provability Induction plus Θ's representation of
computations. The sentences here are propositional rather than first-order Gödel syntax, so
the representation step is exposed as a narrow interface whose fields mention only sentence
emission and eventual theoremhood or refutability — never market prices, and never a
desired asymptotic conclusion.

Those interfaces are the Tier-2 frozen structures `RepresentedSemidecidableClaims`,
`RepresentedDecidableClaims` (which adds the negative half) and `InconsistentTheoryClaims`.
All three are instantiated and discharged in
`Construction/Knowledge/Endpoints.lean`.

`CodeHalts` and `CodeHaltsWithin` name the two computations: unbounded halting, and
termination within a fixed interpreter clock — decidable, and what `thm:dontwait`
represents. `InconsistentTheoryClaims.consistencySentence` is the paper's `⌜Θ′⌝ is
consistent`, recovered syntactically as the negation of the inconsistency sentence, so
`thm:incons`'s second conjunct costs no further representation premise.

`lic_belief_finitistic_consistency` takes the *semidecidable* premise deliberately: every
day's claim is true, so the negative field of a decidable bundle is unreachable, and callers
holding one pass its `.toRepresentedSemidecidableClaims` projection.
`lic_disbelief_inconsistent_theories` is the abstract boundary rather than the content:
`inconsistent` and `hall` index the bundle by the property its witness must establish, and
what makes it a theorem about *theories* lives entirely in the witness, where
`inconsistent n` becomes `¬Entailment.Consistent (theoryOf (m n))` (`dd:machinetheory`).

Counting and reading conventions are cited rather than restated: `dd:symbolcount` for the
finite proof searches, `dd:machinetheory` for reading a machine as a theory.
-/

namespace LogicalInduction

open Filter Topology

/-! ## Representation interfaces -/

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

/-! ## The computations being represented -/

/-- Halting of one `Nat.Partrec.Code` machine on one natural-number input. -/
def CodeHalts (machine : Nat.Partrec.Code) (input : ℕ) : Prop :=
  (machine.eval input).Dom

/-- Termination within a fixed interpreter clock.  Unlike unbounded halting, this predicate
is decidable and is the computation represented in `thm:dontwait`. -/
def CodeHaltsWithin (machine : Nat.Partrec.Code) (input steps : ℕ) : Prop :=
  (Nat.Partrec.Code.evaln steps machine input).isSome = true

/-- The emitted “`⌜Θ′ₙ⌝` is inconsistent” family.  One sentence sequence, not two: the paper
takes `⌜Θ′⌝ is consistent` as primitive and `⌜Θ′⌝ is inconsistent` for its negation
(tex:1861-1865), and this rendering carries the opposite orientation — the *inconsistency*
family is the field, and `consistencySentence` below recovers the other one syntactically.
One family suffices because `Sentence` is Foundation's propositional `Formula`, which
carries a syntactic negation.  The inversion is a rendering choice rather than an identity:
Foundation spells `∼φ` as `φ 🡒 ⊥`, so the Lean consistency sentence is the paper's own
consistency sentence doubly negated.  Nothing downstream reads a sentence's internal shape,
so the two orientations are interchangeable for every claim made here.
Paper node: `thm:incons` -/
structure InconsistentTheoryClaims (DP : DeductiveProcess) (inconsistent : ℕ → Prop) where
  inconsistencySentence : ℕ → Sentence
  inconsistency_poly : BigSentenceCodes inconsistencySentence
  inconsistency_provable : ∀ n, inconsistent n →
    ∃ k, inconsistencySentence n ∈ DP.D k

/-- **The paper's “`⌜Θ′ₙ⌝` is consistent”**, up to the orientation recorded at
`InconsistentTheoryClaims`: the syntactic negation of the day-`n` inconsistency sentence,
which is the paper's own consistency sentence doubly negated (tex:1861-1865). -/
def InconsistentTheoryClaims.consistencySentence {DP : DeductiveProcess}
    {inconsistent : ℕ → Prop} (R : InconsistentTheoryClaims DP inconsistent) (n : ℕ) :
    Sentence :=
  ∼R.inconsistencySentence n

/-! ## Trust in consistency (`thm:pac`, `thm:incons`) -/

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
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
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
in `Construction/Knowledge/Endpoints.lean`), where `inconsistent n` is
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

/-! ## Reasoning about halting (`thm:halts`, `thm:loops`, `thm:dontwait`) -/

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

end LogicalInduction
